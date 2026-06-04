// The lemma `Frame::lemma_from_raw_manuallydrop_general` previously lived
// here. It bridged `Frame::from_raw`'s post-state (which cleared
// `raw_count` to 0) to a subsequent `ManuallyDrop::new` (which bumped
// `raw_count` back to 1). Under the borrow-protocol redesign,
// `Frame::from_raw` mints the obligation directly and `ManuallyDrop::new`
// consumes it — no intermediate bookkeeping debt to discharge.
