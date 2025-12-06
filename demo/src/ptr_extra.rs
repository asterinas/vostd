#[macro_export]
macro_rules! borrow_field {
    ($ptr:expr => $field:tt, NonNull) => {
        (unsafe { $ptr.as_mut() }).$field
    };
}

#[macro_export]
macro_rules! update_field {
    ($ptr:expr => $field:tt <- $val:expr, NonNull) => {
        let __ptr = unsafe { $ptr.as_mut() };
        __ptr.$field = $val;
    };
    ($ptr:expr => $field:tt <- $val:expr) => {
        $ptr.$field = $val;
    };
    ($ptr:expr => $field:tt += $val:expr) => {
        $ptr.$field = $ptr.$field + $val;
    };
    ($ptr:expr => $field:tt -= $val:expr) => {
        $ptr.$field = $ptr.$field - $val;
    };
    ($ptr:expr => $field:tt <- $val:expr, &mut) => {
        $ptr.$field = $val;
    };
    ($ptr:expr => $field:tt += $val:expr, &mut) => {
        $ptr.$field = $ptr.$field + $val;
    };
    ($ptr:expr => $field:tt -= $val:expr, &mut) => {
        $ptr.$field = $ptr.$field - $val;
    };
}
