use vstd::prelude::*;
use crate::{common::*, error::Error};

verus! {

pub open spec fn collect_spec_success(res: Result<Vec<u8>>, len: usize) -> bool {
    res.is_ok() && {
        let buf = res.unwrap();
        buf.len() == len
    }
}

pub open spec fn collect_spec_failure(
    res: Result<Vec<u8>>,
    cursor_old: usize,
    cursor_new: usize,
) -> bool {
    res.is_err() && cursor_old == cursor_new
}

} // verus!
verus! {

pub open spec fn fill_zeros_success(
    res: core::result::Result<usize, (Error, usize)>,
    avail_old: usize,
    avail_new: usize,
) -> bool {
    res.is_ok() && {
        let len = res.unwrap();
        avail_old == avail_new + len
    }
}

pub open spec fn fill_zeros_failure(
    res: core::result::Result<usize, (Error, usize)>,
    avail_old: usize,
    avail_new: usize,
) -> bool {
    res.is_err() && {
        let (err, len) = res.unwrap_err();
        err == Error::PageFault && avail_old == avail_new + len
    }
}

} // verus!
