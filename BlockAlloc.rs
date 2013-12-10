#[feature(macro_rules)];
#[allow(dead_code)];
#[allow(unused_variable)];

extern mod std;
use std::libc::size_t;
use std::ptr;
use std::util::{Void,replace};
#[test]
use std::mem::size_of;
use std::cmp::Eq;
use std::borrow::ref_eq;

fn main() {
    println("hello?");
}

type nat = uint;
type voidptr = *mut Void;

// An MBlock is simply a region of memory whose size is a multiple of
// MBLOCK_SIZE, aligned to an MBLOCK_SIZE boundary.  This is the unit
// by which we allocate memory from the operating system; we then divide
// the megablock into blocks.

static MBLOCK_SHIFT: uint = 20;
static MBLOCK_SIZE: uint = 1 << MBLOCK_SHIFT;

struct MBlock {
    ptr: *mut u8
}

extern {
    pub fn aligned_alloc(align: size_t, size: size_t) -> *mut u8;
    pub fn free(ptr: *mut u8);
}

// XXX: aligned_alloc is a bit more inefficient than manually mmap'ing
// the memory yourself, but it will do for now.
#[inline]
pub unsafe fn aligned_alloc_raw(align: size_t, size: size_t) -> *mut u8 {
    let ptr = aligned_alloc(align, size);
    if ptr == 0 as *mut u8 {
        fail!("out of memory")
    }
    ptr
}

impl MBlock {
    pub fn new(n: nat) -> MBlock {
        unsafe {
            let ptr = aligned_alloc_raw(MBLOCK_SIZE as size_t, (MBLOCK_SIZE * n) as size_t);
            assert!(!ptr::is_null(ptr))
            MBlock{ptr: ptr}
        }
    }
}

impl Eq for MBlock {
    fn eq (&self, other: &MBlock) -> bool {
        return self.ptr == other.ptr;
    }
}

impl Drop for MBlock {
    fn drop (&mut self) {
        unsafe {
            free(self.ptr as *mut u8)
        }
    }
}

// Block manager

static BLOCK_SHIFT: uint = 12;
static BLOCK_SIZE: uint = 1 << BLOCK_SHIFT;
static BLOCK_MASK: uint = BLOCK_SIZE - 1;

static BDESCR_SHIFT: uint = 6;
static BDESCR_SIZE: uint = 1 << BDESCR_SHIFT;
static BDESCR_MASK: uint = BDESCR_SIZE - 1;

macro_rules! BLOCK_ROUND_UP(
    ($p:expr) => (($p + BLOCK_SIZE - 1) & !BLOCK_MASK);
)
pub fn BLOCK_ROUND_UP(p: uint) -> uint {
    BLOCK_ROUND_UP!(p)
}

static FIRST_BLOCK_OFF: uint = BLOCK_ROUND_UP!(BDESCR_SIZE * (MBLOCK_SIZE / BLOCK_SIZE));
static BLOCKS_PER_MBLOCK: uint = (MBLOCK_SIZE - FIRST_BLOCK_OFF) / BLOCK_SIZE;

// Per Rust's ownership types, we conflate a block descriptor with the
// block itself.
struct BlockData {
    start: *mut u8,
    free: *mut u8,
}
struct BlockMeta {
    u: voidptr, // actually a union
    gen: voidptr,

    gen_no: u16,
    dest_no: u16,
    _pad1: u16,
    flags: u16,

    blocks: u32,
    padding: [u32, .. 3]
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

macro_rules! MBLOCK_GROUP_BLOCKS(
    ($p:expr) => (BLOCKS_PER_MBLOCK + ($p - 1) * (MBLOCK_SIZE / BLOCK_SIZE));
)
#[inline]
pub fn MBLOCK_GROUP_BLOCKS(p: uint) -> uint {
    MBLOCK_GROUP_BLOCKS!(p)
}

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
    // requires sm lock
    pub unsafe fn alloc_group(n: nat) -> ~Block {
        if n == 0 {
            fail!("allocGroup: requested zero blocks");
        }
        if n >= BLOCKS_PER_MBLOCK {
            fail!("allocGroup: large allocations not implemented yet")
        }
        n_alloc_blocks += n; // unsafe

        let mut ln = log_2_ceil(n);
        while (ln < MAX_FREE_LIST && free_list[ln].empty()) {
            ln += 1;
        }
        let ln = ln;

        if ln == MAX_FREE_LIST {
        }

        fail!("unimplemented")
    }

    pub unsafe fn alloc_mega_group(mblocks: nat) -> ~Block {
        let n = MBLOCK_GROUP_BLOCKS(mblocks);
        enum SearchResult<'a> {
            PerfectMatch(~Block),
            BestMatch(&'a mut BlockData, &'a mut BlockMeta),
            NoMatch
        }
        //let mut prev_link = &mut free_mblock_list.p;
        //let mut best: Option<(&mut BlockData, &mut BlockMeta)> = None

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
        match go(n, &mut free_mblock_list.p, None) {
            // We found a perfect match and removed it from the list
            PerfectMatch(p) => p,
            // Take our chunk off the end of the best match
            BestMatch(_, _) => fail!("ni"),
            // Nothing in the free list was big enough, so allocate
            NoMatch => fail!("ni"),
        }
    }
}
