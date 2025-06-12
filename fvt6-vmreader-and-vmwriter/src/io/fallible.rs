use vstd::prelude::*;
use core::result::Result;
use super::vmrw::{VmReader, VmWriter};
use crate::{common::*, error::Error, io::model::VmIoModel};

verus! {

pub open spec fn rw_fallibal_spec_success(
    res: Result<usize, (Error, usize)>,
    r_cursor_old: usize,
    r_cursor: usize,
    r_model: &VmIoModel,
    w_cursor_old: usize,
    w_cursor: usize,
    w_model: &VmIoModel,
) -> bool {
    res.is_ok() && {
        let copied_len = res.unwrap();

        r_cursor_old + copied_len == r_cursor && w_cursor_old + copied_len == w_cursor && (r_cursor
            == r_model.end || w_cursor == w_model.end)
    }
}

pub open spec fn rw_fallibal_spec_failure(
    res: Result<usize, (Error, usize)>,
    r_cursor_old: usize,
    r_cursor: usize,
    r_model: &VmIoModel,
    w_cursor_old: usize,
    w_cursor: usize,
    w_model: &VmIoModel,
) -> bool {
    res.is_err() && {
        let (err, copied_len) = res.unwrap_err();

        err == Error::PageFault && r_model.cursor_within_range(
            pnt_sub_spec(r_cursor, copied_len) as usize,
        ) && w_model.cursor_within_range(pnt_sub_spec(w_cursor, copied_len) as usize)
            && r_cursor_old + copied_len == r_cursor && w_cursor_old + copied_len == w_cursor
    }
}

pub open spec fn rw_fallibal_spec(
    res: Result<usize, (Error, usize)>,
    r_cursor_old: usize,
    r_cursor: usize,
    r_model: &VmIoModel,
    w_cursor_old: usize,
    w_cursor: usize,
    w_model: &VmIoModel,
) -> bool {
    rw_fallibal_spec_success(res, r_cursor_old, r_cursor, r_model, w_cursor_old, w_cursor, w_model)
        || rw_fallibal_spec_failure(
        res,
        r_cursor_old,
        r_cursor,
        r_model,
        w_cursor_old,
        w_cursor,
        w_model,
    )
}

pub fn rw_fallible<FallibilityR, FallibilityW>(
    reader: &mut VmReader<'_, FallibilityR>,
    writer: &mut VmWriter<'_, FallibilityW>,
) -> (res: Result<usize, (Error, usize)>)
    requires
        old(reader).invariants(),
        old(writer).invariants(),
    ensures
        reader.invariants(),
        old(reader).invariants_mut(reader),
        writer.invariants(),
        old(writer).invariants_mut(writer),
        rw_fallibal_spec(
            res,
            old(reader).cursor as usize,
            reader.cursor as usize,
            &reader.state@,
            old(writer).cursor as usize,
            writer.cursor as usize,
            &writer.state@,
        ),
{
    let copy_len = if reader.remain() < writer.avail() {
        reader.remain()
    } else {
        writer.avail()
    };
    if copy_len == 0 {
        return Ok(0);
    }
    // SAFETY: The source and destination are subsets of memory ranges specified by
    // the reader and writer, so they are either valid for reading and writing or in
    // user space.

    let copied_len = unsafe {
        let copied_len = memcpy_fallible(writer.cursor, reader.cursor, copy_len);
        reader.cursor = pnt_add(reader.cursor, copied_len);
        writer.cursor = mut_pnt_add(writer.cursor, copied_len);
        copied_len
    };
    if copied_len < copy_len {
        Err((Error::PageFault, copied_len))
    } else {
        Ok(copied_len)
    }
}

} // verus!
