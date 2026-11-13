use ostd_pod::Pod;

#[test]
fn derive_const_generic() {
    #[derive(Debug, Clone, Copy, Pod, PartialEq, Eq)]
    #[repr(C)]
    pub struct Str<const N: usize>([u8; N]);

    let str = Str([0x42, 0x75, 0x66, 0x66, 0x65]);
    let bytes = str.as_bytes();
    assert_eq!(bytes, &[0x42, 0x75, 0x66, 0x66, 0x65]);

    let str2 = Str::from_bytes(bytes);
    assert_eq!(str, str2);
}

#[test]
fn derive_generic() {
    #[derive(Debug, Clone, Copy, Pod, PartialEq, Eq)]
    #[repr(C)]
    pub struct Item<T> {
        value: T,
    }

    let item = Item {
        value: [0x42u8, 0x75, 0x66, 0x66, 0x65],
    };
    let bytes = item.as_bytes();
    assert_eq!(bytes, &[0x42, 0x75, 0x66, 0x66, 0x65]);

    let item2 = Item::from_bytes(bytes);
    assert_eq!(item, item2);
}

#[test]
fn derive_union() {
    #[derive(Clone, Copy, Pod)]
    #[repr(C)]
    pub union Union {
        slice: [u8; 8],
        integer: u32,
    }

    let u = Union { slice: [0x11; 8] };
    let bytes = u.as_bytes();
    assert_eq!(bytes, &[0x11; 8]);
    let u2 = Union::from_bytes(bytes);
    let integer = unsafe { u2.integer };
    assert_eq!(integer, 0x11111111);
}
