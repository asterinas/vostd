use vstd::prelude::*;

verus! {

#[verifier::ext_equal]
pub struct BitMapping<T, U> {
    pub src: T,
    pub dst: U,
}

} // verus!
verus! {

pub trait MapForwardTrait<Dst>: Sized {
    spec fn map_forward_spec(self, bm: &[BitMapping<Self, Dst>]) -> Dst;

    #[verifier::when_used_as_spec(map_forward_spec)]
    fn map_forward(self, bm: &[BitMapping<Self, Dst>]) -> Dst
        returns
            self.map_forward_spec(bm),
    ;

    broadcast proof fn lemma_equal_map_froward(
        x: Self,
        y: Self,
        bm1: &[BitMapping<Self, Dst>],
        bm2: &[BitMapping<Self, Dst>],
    )
        requires
            x == y,
            bm1 == bm2,
        ensures
            #[trigger] x.map_forward_spec(bm1) == #[trigger] y.map_forward_spec(bm2),
    ;
}

} // verus!
macro_rules! impl_map_forward {
    ($src:ty, $dst:ty) => {
        verus! {
        impl MapForwardTrait<$dst> for $src {
            open spec fn map_forward_spec(self, bm: &[BitMapping<Self, $dst>]) -> $dst {
                bm@.fold_left(0 as $dst, |acc: $dst, m: BitMapping<Self, $dst>| {
                    if self & m.src == m.src {
                        acc | m.dst
                    } else {
                        acc
                    }
                })
            }

            #[verifier::external_body]
            fn map_forward(self, bm: &[BitMapping<Self, $dst>]) -> $dst
            {
                bm.iter().fold(0 as $dst, |acc, m| {
                    if self & m.src == m.src {
                        acc | m.dst
                    } else {
                        acc
                    }
                })
            }

            proof fn lemma_equal_map_froward(x: Self, y: Self,
                bm1: &[BitMapping<Self, $dst>], bm2: &[BitMapping<Self, $dst>])
            { }
        }
        }
    };
}

verus! {

pub trait MapInvertForwardTrait<Dst>: Sized {
    spec fn map_invert_forward_spec(self, bm: &[BitMapping<Self, Dst>]) -> Dst;

    #[verifier::when_used_as_spec(map_invert_forward_spec)]
    fn map_invert_forward(self, bm: &[BitMapping<Self, Dst>]) -> Dst
        returns
            self.map_invert_forward_spec(bm),
    ;

    broadcast proof fn lemma_equal_map_invert_froward(
        x: Self,
        y: Self,
        bm1: &[BitMapping<Self, Dst>],
        bm2: &[BitMapping<Self, Dst>],
    )
        requires
            x == y,
            bm1 == bm2,
        ensures
            #[trigger] x.map_invert_forward(bm1) == #[trigger] y.map_invert_forward(bm2),
    ;
}

} // verus!
macro_rules! impl_map_invert_forward {
    ($src:ty, $dst:ty) => {
        verus! {
        impl MapInvertForwardTrait<$dst> for $src {
            open spec fn map_invert_forward_spec(self, bm: &[BitMapping<Self, $dst>]) -> $dst {
                let inv_src = !self;
                bm@.fold_left(0 as $dst, |acc: $dst, m: BitMapping<Self, $dst>| {
                    if inv_src & m.src == 0 {
                        acc | m.dst
                    } else {
                        acc
                    }
                })
            }

            #[verifier::external_body]
            fn map_invert_forward(self, bm: &[BitMapping<Self, $dst>]) -> $dst
            {
                let inv_src = !self;
                bm.iter().fold(0 as $dst, |acc, m| {
                    if inv_src & m.src == 0 {
                        acc | m.dst
                    } else {
                        acc
                    }
                })
            }

            proof fn lemma_equal_map_invert_froward(x: Self, y: Self,
                bm1: &[BitMapping<Self, $dst>], bm2: &[BitMapping<Self, $dst>])
            { }
        }
        }
    };
}

verus! {

pub trait MapBackward<Src>: Sized {
    spec fn map_backward_spec(self, bm: &[BitMapping<Src, Self>]) -> Src;

    #[verifier::when_used_as_spec(map_backward_spec)]
    fn map_backward(self, bm: &[BitMapping<Src, Self>]) -> Src
        returns
            self.map_backward_spec(bm),
    ;

    broadcast proof fn lemma_equal_map_backward(
        x: Self,
        y: Self,
        bm1: &[BitMapping<Src, Self>],
        bm2: &[BitMapping<Src, Self>],
    )
        requires
            x == y,
            bm1 == bm2,
        ensures
            #[trigger] x.map_backward(bm1) == #[trigger] y.map_backward(bm2),
    ;
}

} // verus!
macro_rules! impl_map_backward {
    ($src:ty, $dst:ty) => {
        verus! {
        impl MapBackward<$src> for $dst {

            open spec fn map_backward_spec(self, bm: &[BitMapping<$src, Self>]) -> $src {
                bm@.fold_left(0 as $src, |acc: $src, m: BitMapping<$src, Self>| {
                    if self & m.dst == m.dst {
                        acc | m.src
                    } else {
                        acc
                    }
                })
            }

            #[verifier::external_body]
            fn map_backward(self, bm: &[BitMapping<$src, Self>]) -> $src
            {
                bm.iter().fold(0 as $src, |acc, m| {
                    if self & m.dst == m.dst {
                        acc | m.src
                    } else {
                        acc
                    }
                })
            }

            proof fn lemma_equal_map_backward(x: Self, y: Self,
                bm1: &[BitMapping<$src, Self>], bm2: &[BitMapping<$src, Self>])
            { }
        }
        }
    };
}

verus! {

pub trait MapInvertBackward<Src>: Sized {
    spec fn map_invert_backward_spec(self, bm: &[BitMapping<Src, Self>]) -> Src;

    #[verifier::when_used_as_spec(map_invert_backward_spec)]
    fn map_invert_backward(self, bm: &[BitMapping<Src, Self>]) -> Src
        returns
            self.map_invert_backward_spec(bm),
    ;

    broadcast proof fn lemma_equal_map_invert_backward(
        x: Self,
        y: Self,
        bm1: &[BitMapping<Src, Self>],
        bm2: &[BitMapping<Src, Self>],
    )
        requires
            x == y,
            bm1 == bm2,
        ensures
            #[trigger] x.map_invert_backward(bm1) == #[trigger] y.map_invert_backward(bm2),
    ;
}

} // verus!
macro_rules! impl_map_invert_backward {
    ($src:ty, $dst:ty) => {
        verus! {
        impl MapInvertBackward<$src> for $dst {

            open spec fn map_invert_backward_spec(self, bm: &[BitMapping<$src, Self>]) -> $src {
                let inv_src = !self;
                bm@.fold_left(0 as $src, |acc: $src, m: BitMapping<$src, Self>| {
                    if inv_src & m.dst == 0 {
                        acc | m.src
                    } else {
                        acc
                    }
                })
            }

            #[verifier::external_body]
            fn map_invert_backward(self, bm: &[BitMapping<$src, Self>]) ->  $src
            {
                let inv_src = !self;
                bm.iter().fold(0 as $src, |acc, m| {
                    if inv_src & m.dst == 0 {
                        acc | m.src
                    } else {
                        acc
                    }
                })
            }

            proof fn lemma_equal_map_invert_backward(x: Self, y: Self,
                bm1: &[BitMapping<$src, Self>], bm2: &[BitMapping<$src, Self>])
            { }
        }
        }
    };
}

macro_rules! impl_map_operations {
    ($src:ty, $dst:ty) => {
        impl_map_forward!($src, $dst);
        impl_map_invert_forward!($src, $dst);
        impl_map_backward!($src, $dst);
        impl_map_invert_backward!($src, $dst);
    };
}

impl_map_operations!(u8, u8);
impl_map_operations!(u8, u16);
impl_map_operations!(u8, u32);
impl_map_operations!(u8, u64);
impl_map_operations!(u8, usize);

impl_map_operations!(u32, u32);
impl_map_operations!(u32, u64);
impl_map_operations!(u32, usize);

impl_map_operations!(u64, u64);
impl_map_operations!(u64, usize);

verus! {


} // verus!
#[macro_export]
macro_rules! bm {
    ($src: expr, $dst: expr) => {
        BitMapping {
            src: $src,
            dst: $dst,
        }
    };
}

pub use bm;

#[macro_export]
macro_rules! bms {
    ($(($src:expr, $dst:expr)), * $(,)?) => {
    [
        $(BitMapping { src: $src, dst: $dst }, )*
    ]
    };
}

pub use bms;

#[macro_export]
macro_rules! bms_as {
    ($src_ty:ty, $dst_ty:ty, [ $( ($src:expr, $dst:expr) ),* $(,)? ]) => {
    [
        $(BitMapping { src: $src as $src_ty, dst: $dst as $dst_ty }, )*
    ]
    };
}

pub use bms_as;

#[macro_export]
macro_rules! decl_bms_const {
    ($name:ident, $spec_name:ident, $type1:ty, $type2:ty, $len:expr, [$($flags:expr),* $(,)?]) => {
        verus! {
        pub spec const $spec_name: [BitMapping<$type1, $type2>; $len] = bms![
            $($flags),*
        ];

        #[verifier::when_used_as_spec($spec_name)]
        pub exec const $name: [BitMapping<$type1, $type2>; $len] = bms![
            $($flags),*
        ];
    }
    };
}

pub use decl_bms_const;
