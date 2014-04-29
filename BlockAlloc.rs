#[feature(macro_rules)];
#[allow(dead_code)];
#[allow(unused_variable)];
#[allow(unreachable_code)];
#[allow(unused_mut)];

extern mod std;
use std::libc::size_t;
use std::ptr;
use std::util::{Void,replace};
#[test]
use std::mem::size_of;
use std::cmp::Eq;
use std::borrow::ref_eq;

fn main() {}

type nat = uint; // NB: different from GHC's nat, which may only be 32-bits
type voidptr = *mut Void;

// Constants

static MBLOCK_SHIFT: uint = 20;
static MBLOCK_SIZE: uint = 1 << MBLOCK_SHIFT;
static MBLOCK_MASK: uint = MBLOCK_SIZE - 1;

static BLOCK_SHIFT: uint = 12;
static BLOCK_SIZE: uint = 1 << BLOCK_SHIFT;
static BLOCK_MASK: uint = BLOCK_SIZE - 1;

static BDESCR_SHIFT: uint = 6;
static BDESCR_SIZE: uint = 1 << BDESCR_SHIFT;
static BDESCR_MASK: uint = BDESCR_SIZE - 1;

// An oddity: the round up macros are only ever used on numbers, but
// the round down is only ever used on pointers

macro_rules! BLOCK_ROUND_UP(
    ($n:expr) => (($n + BLOCK_SIZE - 1) & !BLOCK_MASK);
)
pub fn BLOCK_ROUND_UP(n: uint) -> uint { BLOCK_ROUND_UP!(n) }

static FIRST_BLOCK_OFF: uint = BLOCK_ROUND_UP!(BDESCR_SIZE * (MBLOCK_SIZE / BLOCK_SIZE));
static BLOCKS_PER_MBLOCK: uint = (MBLOCK_SIZE - FIRST_BLOCK_OFF) / BLOCK_SIZE;

pub fn MBLOCK_ROUND_UP(n: uint) -> uint {
    (n + MBLOCK_SIZE - 1) & !MBLOCK_MASK
}

pub fn BLOCKS_TO_MBLOCKS(n: uint) -> uint {
    1 + MBLOCK_ROUND_UP((n - BLOCKS_PER_MBLOCK) * BLOCK_SIZE) / MBLOCK_SIZE
}

macro_rules! MBLOCK_GROUP_BLOCKS(
    ($n:expr) => (BLOCKS_PER_MBLOCK + ($n - 1) * (MBLOCK_SIZE / BLOCK_SIZE));
)
#[inline]
pub fn MBLOCK_GROUP_BLOCKS(n: uint) -> uint {
    MBLOCK_GROUP_BLOCKS!(n)
}

/// Unsafely convert a `uint` into a `RawPtr` to any type; inverse of `RawPtr::to_uint()`.
pub unsafe fn to_ptr<T>(p: uint) -> *mut T { std::cast::transmute(p) }

/// Unsafely cast between two `RawPtr`s.
pub unsafe fn cast_ptr<T,S>(p: *mut T) -> *mut S { std::cast::transmute(p) }

// An MBlock (group) is simply a region of memory whose size is a multiple of
// MBLOCK_SIZE, aligned to an MBLOCK_SIZE boundary.  This is the unit
// by which we allocate memory from the operating system; we then divide
// the megablock into blocks.
//
// We can also view an MBlock through its very first block descriptor
// (actually, the start pointer

struct MBlockData {
    start: voidptr,
    priv _pad: uint,
}

struct MBlockMeta {
    priv _pad1: [uint, .. 3],
    blocks: u32,
    priv _pad2: [u32, .. 3]
}

/*
struct MBlock {
    data: MBlockData,
    link: Chain,
    meta: MBlockMeta
}
*/

struct MBlock {
    ptr: voidptr
}

extern {
    pub fn aligned_alloc(align: size_t, size: size_t) -> voidptr;
    pub fn free(ptr: voidptr);
}

// XXX: aligned_alloc is a bit more inefficient than manually mmap'ing
// the memory yourself, but it will do for now.
//
// XXX: We can't do deallocation using aligned_alloc, since we don't
// record the original chunks of memory we allocated, and we need to
// pass the original starting pointer back to free.  (We don't have this
// problem with the manual mmap, since we can incrementally munmap
// regions of memory we may have allocated in one go previously.
#[inline]
pub unsafe fn aligned_alloc_raw(align: size_t, size: size_t) -> voidptr {
    let ptr = aligned_alloc(align, size);
    if ptr.is_null() {
        fail!("out of memory")
    }
    ptr
}

impl MBlock {
    pub fn new(n: nat) -> MBlock {
        let ptr = unsafe { aligned_alloc_raw(MBLOCK_SIZE as size_t, (MBLOCK_SIZE * n) as size_t) };
        assert!(!ptr::is_null(ptr));
        let mb = MBlock{ptr: ptr};
        // XXX should this really be here?
        // One might argue that this should occur in block
        // initialization.  However, this is not really true:
        // invariant of MBlock is the start pointers of the first MBlock
        // are ininitialized.
        unsafe {
            let mut block = mb.first_block_ptr();
            let mut bd = mb.first_bdescr_ptr();
            while (block <= mb.last_block_ptr()) {
                (*bd).data.start = cast_ptr(block);
                bd = bd.offset(1);
                block = block.offset(BLOCK_SIZE as int);
            }
        }
        mb
    }

    // NB: We're not actually interested in null MBlock pointers, so
    // we didn't implement all of RawPtr
    pub fn to_uint(&self) -> uint {
        self.ptr.to_uint()
    }

    pub unsafe fn to_block(~self) -> ~Block {
        fail!("whoops")
    }

    pub unsafe fn first_block_ptr(&self) -> *mut u8 {
        to_ptr(FIRST_BLOCK_OFF + self.to_uint())
    }

    pub unsafe fn last_block_ptr(&self) -> *mut u8 {
        to_ptr(MBLOCK_SIZE - BLOCK_SIZE + self.to_uint())
    }

    pub unsafe fn first_bdescr_ptr(&self) -> *mut Block {
        to_ptr((FIRST_BLOCK_OFF >> (BLOCK_SHIFT - BDESCR_SHIFT)) + self.to_uint())
    }

    //pub unsafe fn FIRST_BDESCR(m: voidptr)
}

impl Eq for MBlock {
    fn eq (&self, other: &MBlock) -> bool {
        return self.ptr == other.ptr;
    }
}

impl Drop for MBlock {
    fn drop (&mut self) {
        unsafe {
            free(self.ptr)
        }
    }
}

// Block manager

// Per Rust's ownership types, we conflate a block descriptor with the
// block itself.
struct BlockData {
    start: voidptr,
    free: voidptr,
}
struct BlockMeta {
    u: voidptr, // actually a union
    gen: voidptr,

    gen_no: u16,
    dest_no: u16,
    priv _pad1: u16,
    flags: u16,

    blocks: u32,
    priv _pad2: [u32, .. 3]
}
struct Block {
    data: BlockData,
    link: Chain,
    meta: BlockMeta
}

struct Chain {
    p: Option<~Block>
}

impl Eq for Block {
    fn eq (&self, other: &Block) -> bool {
        return ref_eq(self, other);
    }
}

impl Chain {
    #[inline]
    fn none() -> Chain {
        return Chain{p: None};
    }
    #[inline]
    fn empty(&self) -> bool {
        return self.p == None;
    }
    #[inline]
    fn iter<'a>(&'a self) -> ChainIterator<'a> {
        return ChainIterator{elem: self};
    }
}

struct ChainIterator<'a> {
    elem: &'a Chain
}

struct MutChainIterator<'a> {
    elem: Option<&'a mut Block>
}

impl<'a> Iterator<&'a Block> for ChainIterator<'a> {
    fn next(&mut self) -> Option<&'a Block> {
        match self.elem.p {
            None => None,
            Some(~ref p) => {
                self.elem = &p.link;
                Some(p)
            }
        }
    }
}

// NB: We can't return mutable Block, because it contains link and would
// cause an iterator invalidation problem.  Note that *no copying occurs*
impl<'a> Iterator<(&'a mut BlockData, &'a mut BlockMeta)> for MutChainIterator<'a> {
    fn next(&mut self) -> Option<(&'a mut BlockData, &'a mut BlockMeta)> {
        // work-around the borrow checker
        //  XXX unfortunately, this has runtime consequences
        let x = std::util::replace(&mut self.elem, None);
        let (nelem, result) = match x {
            None => (None, None),
            // XXX s/data: ref mut data/ref mut data/ when fix hits
            Some(&Block {data: ref mut data, link: ref mut link, meta: ref mut meta}) => {
                (match link.p {
                    None => None,
                    Some(~ref mut p) => Some(p)
                }, Some((data,meta)))
            }
        };
        self.elem = nelem;
        result
    }
}

#[test]
fn check_size_block() {
    assert_eq!(size_of::<Block>(), 64);
}

// working around https://github.com/mozilla/rust/issues/5244
macro_rules! EMPTY_CHAIN(() => (Chain {p: None});)

static MAX_FREE_LIST: nat = 9;
static mut free_list: [Chain, .. MAX_FREE_LIST] = [EMPTY_CHAIN!(), EMPTY_CHAIN!(), EMPTY_CHAIN!(), EMPTY_CHAIN!(), EMPTY_CHAIN!(), EMPTY_CHAIN!(), EMPTY_CHAIN!(), EMPTY_CHAIN!(), EMPTY_CHAIN!(), ];
static mut free_mblock_list: Chain = EMPTY_CHAIN!();
static mut n_alloc_blocks: uint = 0;

#[inline]
fn log_2_ceil(n: nat) -> nat {
    let mut x = 1;
    for i in range(0, MAX_FREE_LIST) {
        if x >= n { return i; }
        x = x << 1;
    }
    return MAX_FREE_LIST;
}

impl Block {
    // REQUIRES SM LOCK
    pub fn alloc_group(n: nat) -> ~Block {
        if n == 0 {
            fail!("allocGroup: requested zero blocks");
        }
        if n >= BLOCKS_PER_MBLOCK {
            fail!("allocGroup: large allocations not implemented yet")
        }
        unsafe { n_alloc_blocks += n };

        let mut ln = log_2_ceil(n);
        while (ln < MAX_FREE_LIST && unsafe { free_list[ln].empty() }) {
            ln += 1;
        }
        let ln = ln;

        if ln == MAX_FREE_LIST {
        }

        fail!("unimplemented")
    }

    // REQUIRES SM LOCK
    pub fn alloc_mega_group(mblocks: nat) -> ~Block {
        let n = MBLOCK_GROUP_BLOCKS(mblocks);
        enum SearchResult<'a> {
            PerfectMatch(~Block),
            BestMatch(&'a mut BlockData, &'a mut BlockMeta),
            NoMatch
        }
        // tail-recursive style makes the borrow-checker *a lot*
        // happier, since some of the aliasing effects that occur when
        // local mutable variables are reused go away (fresh lexical
        // scope, fresh lifetime, it's great)
        fn go<'a>(n: uint,
                  prev_link: &'a mut Option<~Block>,
                  best: Option<(&'a mut BlockData, &'a mut BlockMeta)>)
          -> SearchResult<'a> {
            match prev_link {
                &None => match best {
                    None => NoMatch,
                    Some((data, meta)) => BestMatch(data, meta)
                },
                // NB: need to match it out, so we don't take out a
                // reference on prev_link that will interfere with the
                // take()
                &Some(~Block {meta: BlockMeta {blocks, ..}, ..}) if blocks as uint == n => {
                    let mut bd = prev_link.take_unwrap();
                    *prev_link = bd.link.p.take();
                    PerfectMatch(bd)
                },
                &Some(ref mut bd) => {
                    if bd.meta.blocks as uint > n && match best {
                        None => true,
                        Some((_, ref best_meta)) => bd.meta.blocks < best_meta.blocks
                    } {
                        go(n, &mut bd.link.p, Some((&mut bd.data, &mut bd.meta)))
                    } else {
                        go(n, &mut bd.link.p, best)
                    }
                }
            }
        }
        // NB: global_ref can be used to mutate global state
        let mut global_ref = unsafe { &mut free_mblock_list.p };
        let mut bd: ~Block = match go(n, global_ref, None) {
            // We found a perfect match and removed it from the list
            PerfectMatch(p) => return p,
            // Take our chunk off the end of the best match
            BestMatch(ref data, ref mut meta) => {
                let best_mblocks = BLOCKS_TO_MBLOCKS(meta.blocks as uint);
                // bd = FIRST_BDESCR((StgWord8*)MBLOCK_ROUND_DOWN(best) +·
                //        (best_mblocks-mblocks)*MBLOCK_SIZE);
                meta.blocks = MBLOCK_GROUP_BLOCKS(best_mblocks - mblocks) as u32;
                fail!("initMBlock(MBLOCK_ROUND_DOWN(bd));")
            },
            // Nothing in the free list was big enough, so allocate
            NoMatch => {
                let mut mblock = MBlock::new(mblocks);
                fail!("bd = FIRST_BDESCR(mblock);");
            },
        };
        bd.meta.blocks = MBLOCK_GROUP_BLOCKS(mblocks) as u32;
        return bd
    }
}
