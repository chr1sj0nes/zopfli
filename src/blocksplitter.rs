use std::f64;
use std::iter;

use deflate::calculate_block_size_auto_type;
use lz77::{Lz77Store, ZopfliBlockState};
use Options;

/// Finds minimum of function `f(i)` where `i` is of type `usize`, `f(i)` is of type
/// `f64`, `i` is in range `start-end` (excluding `end`).
/// Returns the index to the minimum and the minimum value.
/// TODO pass Range, rather than start + end
fn find_minimum<F>(f: F, start: usize, end: usize) -> (usize, f64)
    where F: Fn(usize) -> f64
{
    if end - start < 1024 {
        let default = (start, f64::MAX);
        (start..end).map(|i| (i, f(i))).fold(default, |a, b| if b.1 < a.1 { b } else { a })
    } else {
        let mut start = start;
        let mut end = end;
        /* Try to find minimum faster by recursively checking multiple points. */
        const NUM: usize = 9;  /* Good value: 9. ?!?!?!?! */
        let mut lastbest = f64::MAX;
        let mut pos = start;

        let default = (0, start, f64::MAX); // FIXME we don't actually need a default (how do we save one comparison?)

        while end - start > NUM {
            let skip = (end - start) / (NUM + 1);

            let (besti, bestp, best) =
                (0..NUM).map(|i| {
                    let p = start + (i + 1) * skip; // FIXME is this a bug? it never evaluates at start
                    (i, p, f(p))
                }).fold(default, |a, b| if b.2 < a.2 { b } else { a });

            if best > lastbest {
                break;
            }

            start = if besti == 0 { start } else { bestp - skip };
            end = if besti == NUM - 1 { end } else { bestp + skip };

            pos = bestp;
            lastbest = best;
        }
        (pos, lastbest)
    }
}

/// Returns estimated cost of a block in bits.  It includes the size to encode the
/// tree and the size to encode all literal, length and distance symbols and their
/// extra bits.
///
/// litlens: lz77 lit/lengths
/// dists: ll77 distances
/// lstart: start of block
/// lend: end of block (not inclusive)
fn estimate_cost(lz77: &Lz77Store, lstart: usize, lend: usize) -> f64 {
    calculate_block_size_auto_type(lz77, lstart, lend)
}

/// Finds next block to try to split, the largest of the available ones.
/// The largest is chosen to make sure that if only a limited amount of blocks is
/// requested, their sizes are spread evenly.
/// done: array indicating which blocks starting at that position are no longer
///     splittable (splitting them increases rather than decreases cost).
/// splitpoints: the splitpoints found so far.
fn find_largest_splittable_block(done: &[bool], splitpoints: &[usize]) -> Option<(usize, usize)> {
    splitpoints.iter()
    .map(|a| *a).chain(iter::once(done.len() - 1))
    .scan(0, |prev, a| { let r = Some((*prev, a)); *prev = a; r })
    .filter(|&(a, _)| !done[a])
    .max_by_key(|&(a, b)| b - a)
}

/// Prints the block split points as decimal and hex values in the terminal.
fn print_block_split_points(lz77: &Lz77Store, lz77splitpoints: &[usize]) {
    let nlz77points = lz77splitpoints.len();
    let mut splitpoints = Vec::with_capacity(nlz77points);

    /* The input is given as lz77 indices, but we want to see the uncompressed
    index values. */
    let mut pos = 0;
    if nlz77points > 0 {
        for (i, item) in lz77.litlens.iter().enumerate() {
            let length = item.size();
            if lz77splitpoints[splitpoints.len()] == i {
                splitpoints.push(pos);
                if splitpoints.len() == nlz77points {
                    break;
                }
            }
            pos += length;
        }
    }
    assert!(splitpoints.len() == nlz77points);

    println!("block split points: {} (hex: {})", splitpoints.iter().map(|&sp| format!("{}", sp)).collect::<Vec<_>>().join(" "), splitpoints.iter().map(|&sp| format!("{:x}", sp)).collect::<Vec<_>>().join(" "));
}

/// Does blocksplitting on LZ77 data.
/// The output splitpoints are indices in the LZ77 data.
/// maxblocks: set a limit to the amount of blocks. Set to 0 to mean no limit.
pub fn blocksplit_lz77(options: &Options, lz77: &Lz77Store, maxblocks: usize) -> Vec<usize> {
    let mut splitpoints = Vec::with_capacity(maxblocks);

    if lz77.size() < 10 {
        return splitpoints; /* This code fails on tiny files. */
    }

    let mut done = vec![false; lz77.size()];
    let mut lstart = 0;
    let mut lend = lz77.size();

    while maxblocks == 0 || splitpoints.len() < (maxblocks - 1) {
        assert!(lstart < lend);
        let (llpos, splitcost) =
            find_minimum(|i| estimate_cost(lz77, lstart, i) + estimate_cost(lz77, i, lend), lstart + 1, lend);

        assert!(llpos > lstart);
        assert!(llpos < lend);

        let origcost = estimate_cost(lz77, lstart, lend);

        if splitcost > origcost || llpos == lstart + 1 || llpos == lend {
            done[lstart] = true;
        } else {
            splitpoints.push(llpos);
            splitpoints.sort();
        }

        // If `find_largest_splittable_block` returns `None`, no further split will
        // likely reduce compression.
        let is_finished = find_largest_splittable_block(&done, &splitpoints)
            .map_or(true, |(start, end)| {
                lstart = start;
                lend = end;
                lend - lstart < 10
            });

        if is_finished { break }
    }

    if options.verbose {
        print_block_split_points(lz77, &splitpoints);
    }

    splitpoints
}

/// Does blocksplitting on uncompressed data.
/// The output splitpoints are indices in the uncompressed bytes.
///
/// options: general program options.
/// in_data: uncompressed input data
/// instart: where to start splitting
/// inend: where to end splitting (not inclusive)
/// maxblocks: maximum amount of blocks to split into, or 0 for no limit
pub fn blocksplit(options: &Options, in_data: &[u8], instart: usize, inend: usize, maxblocks: usize) -> Vec<usize> {
    let mut store = Lz77Store::new();

    /* Unintuitively, Using a simple LZ77 method here instead of lz77_optimal
    results in better blocks. */
    {
        let mut state = ZopfliBlockState::new_without_cache(options, instart, inend);
        store.greedy(&mut state, in_data, instart, inend);
    }

    let lz77splitpoints = blocksplit_lz77(options, &store, maxblocks);
    let mut splitpoints = Vec::with_capacity(maxblocks);

    /* Convert LZ77 positions to positions in the uncompressed input. */
    let mut pos = instart;
    if lz77splitpoints.len() > 0 {
        for (i, item) in store.litlens.iter().enumerate() {
            if lz77splitpoints[splitpoints.len()] == i {
                splitpoints.push(pos);
                if splitpoints.len() == lz77splitpoints.len() {
                    break;
                }
            }
            pos += item.size();
        }
    }
    assert!(splitpoints.len() == lz77splitpoints.len());
    splitpoints
}
