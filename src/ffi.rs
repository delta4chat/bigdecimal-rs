use super::*;

use stdlib::ffi::c_char;

use stdlib::ffi::{CStr, CString};
use stdlib::sync::Arc;

extern crate concat_idents;
use self::concat_idents::concat_idents;

extern crate once_cell;
use self::once_cell::sync::Lazy;

extern crate portable_atomic;
use self::portable_atomic::{AtomicI64, Ordering::Relaxed};

/*
use bigdecimal::BigDecimal;
use bigdecimal::num_traits::{self, Zero, One, Signed};
use bigdecimal::num_bigint::{BigInt, Sign};
*/

type Index<T> = (scc2::HashIndex<i64, Arc<T>>, scc2::HashIndex<Arc<T>, i64>);
type LazyIndex<T> = Lazy<Index<T>>;

static BIGDECIMAL_INDEX: LazyIndex<BigDecimal> = Lazy::new(Default::default);
static BIGINT_INDEX: LazyIndex<BigInt> = Lazy::new(Default::default);

#[repr(u8)]
#[derive(Copy, Clone, Debug)]
pub enum ID {
    BigDecimal,
    BigInt,
}
impl ID {
    pub fn default(&self) -> Option<i64> {
        static BIGDECIMAL_DEFAULT_ID: AtomicI64 = AtomicI64::new(-1);
        static BIGINT_DEFAULT_ID: AtomicI64 = AtomicI64::new(-1);


        let default_id =
            match self {
                Self::BigDecimal => {
                    &BIGDECIMAL_DEFAULT_ID
                },
                Self::BigInt => {
                    &BIGINT_DEFAULT_ID
                }
            };

        let _ = default_id.fetch_update(Relaxed, Relaxed, |id| {
            if id == -1 {
                Some(self.new()?)
            } else {
                None
            }
        });

        let id = default_id.load(Relaxed);
        if id == -1 {
            None
        } else {
            Some(id)
        }
    }

    pub fn new(&self) -> Option<i64> {
                                                               //     Big Dec
        static BIGDECIMAL_ID_COUNTER: AtomicI64 = AtomicI64::new(0x00_B19_Dec_00000000);

                                                               //     Big Int
        static BIGINT_ID_COUNTER:     AtomicI64 = AtomicI64::new(0x00_B19_111_00000000);

        let counter =
            match self {
                Self::BigDecimal => {
                    &BIGDECIMAL_ID_COUNTER
                },
                Self::BigInt => {
                    &BIGINT_ID_COUNTER
                }
            };

        counter.fetch_update(Relaxed, Relaxed, |id| {
            if id < i64::MAX {
                Some(id + 1)
            } else {
                None
            }
        }).ok()
    }
}


#[allow(non_camel_case_types)]
#[repr(i8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Errno {
    /// No Error but no value avaliable.
    /// (currently used by sqrt/ln/log function)
    NO_ERROR = 0i8,

    /// extern FFI caller provides NULL pointer.
    NULL_POINTER = -1i8,

    /// Signed 64-bit integer ID has been exhausted.
    INT64_ID_EXHAUSTED = -2i8,

    /// Signed 64-bit integer ID of 1nd-argument not found.
    INT64_ID1_NOT_FOUND = -3i8,

    /// Signed 64-bit integer ID of 2nd-argument not found.
    INT64_ID2_NOT_FOUND = -4i8,

    /// Provided string is not numeric.
    INVALID_STRING = -5i8,

    /// Provided radix-of-string is not valid.
    INVALID_RADIX = -6i8,

    /// Division by Zero.
    DIVISION_BY_ZERO = -7i8,

    /// Other unknown error number.
    UNKNOWN_ERRNO = -128i8,
}
impl Errno {
    pub const fn from_i8(i: i8) -> Option<Self> {
        Self::from_i64(i as i64)
    }
    pub const fn from_i64(i: i64) -> Option<Self> {
        if i > 0 {
            return None;
        }

        let mut errno = Self::NO_ERROR;
        if i == errno.to_i64() {
            return Some(errno);
        }

        errno = Self::NULL_POINTER;
        if i == errno.to_i64() {
            return Some(errno);
        }

        errno = Self::INT64_ID_EXHAUSTED;
        if i == errno.to_i64() {
            return Some(errno);
        }

        errno = Self::INT64_ID1_NOT_FOUND;
        if i == errno.to_i64() {
            return Some(errno);
        }
            
        errno = Self::INT64_ID2_NOT_FOUND;
        if i == errno.to_i64() {
            return Some(errno);
        }

        errno = Self::INVALID_STRING;
        if i == errno.to_i64() {
            return Some(errno);
        }

        errno = Self::INVALID_RADIX;
        if i == errno.to_i64() {
            return Some(errno);
        }

        errno = Self::DIVISION_BY_ZERO;
        if i == errno.to_i64() {
            return Some(errno);
        }

        errno = Self::UNKNOWN_ERRNO;
        if i == errno.to_i64() {
            return Some(errno);
        }

        None
    }

    pub const fn to_i8(&self) -> i8 {
        (*self) as i8
    }
    pub const fn to_i64(&self) -> i64 {
        self.to_i8() as i64
    }

    pub const fn to_ascii(&self) -> &'static [u8] {
        match self {
            Self::NO_ERROR => b"NO_ERROR",

            Self::NULL_POINTER => b"NULL_POINTER",

            Self::INT64_ID_EXHAUSTED => b"INT64_ID_EXHAUSTED",
            Self::INT64_ID1_NOT_FOUND => b"INT64_ID1_NOT_FOUND",
            Self::INT64_ID2_NOT_FOUND => b"INT64_ID2_NOT_FOUND",

            Self::INVALID_STRING => b"INVALID_STRING",
            Self::INVALID_RADIX => b"INVALID_RADIX",

            Self::DIVISION_BY_ZERO => b"DIVISION_BY_ZERO",

            Self::UNKNOWN_ERRNO => b"UNKNOWN_ERRNO",
        }
    }
    pub fn from_ascii(s: &[u8]) -> Option<Self> {
        if ! s.is_ascii() {
            return None;
        }
        let s = s.trim_ascii().to_ascii_uppercase();
        match s.as_slice() {
            b"NO_ERROR" => Some(Self::NO_ERROR),

            b"NULL_POINTER" => Some(Self::NULL_POINTER),

            b"INT64_ID_EXHAUSTED" => Some(Self::INT64_ID_EXHAUSTED),
            b"INT64_ID1_NOT_FOUND" => Some(Self::INT64_ID1_NOT_FOUND),
            b"INT64_ID2_NOT_FOUND" => Some(Self::INT64_ID2_NOT_FOUND),

            b"INVALID_STRING" => Some(Self::INVALID_STRING),
            b"INVALID_RADIX" => Some(Self::INVALID_RADIX),

            b"DIVISION_BY_ZERO" => Some(Self::DIVISION_BY_ZERO),

            b"UNKNOWN_ERRNO" => Some(Self::UNKNOWN_ERRNO),

            _ => None
        }
    }

    pub fn to_cstring(&self) -> CString {
        CString::new(self.to_ascii()).unwrap()
    }
    pub fn from_cstr(cstr: &CStr) -> Option<Self> {
        Self::from_ascii(cstr.to_bytes())
    }
}

#[no_mangle]
pub extern fn bignum_str2errno(cstr_ptr: *const c_char) -> i8 {
    if cstr_ptr.is_null() {
        return Errno::NULL_POINTER.to_i8();
    }

    let cstr = unsafe { CStr::from_ptr(cstr_ptr) };
    if let Some(errno) = Errno::from_cstr(cstr) {
        errno.to_i8()
    } else {
        Errno::UNKNOWN_ERRNO.to_i8()
    }
}

#[no_mangle]
pub extern fn bignum_errno2str(e: i8) -> *const c_char {
    if let Some(errno) = Errno::from_i8(e) {
        let cstring = errno.to_cstring();
        let ptr = cstring.as_c_str().as_ptr();
        stdlib::mem::forget(cstring);
        ptr
    } else {
        stdlib::ptr::null()
    }
}

#[no_mangle]
pub extern fn bigdecimal_str2errno(cstr_ptr: *const c_char) -> i8 {
    bignum_str2errno(cstr_ptr)
}

#[no_mangle]
pub extern fn bigdecimal_errno2str(e: i8) -> *const c_char {
    bignum_errno2str(e)
}

#[no_mangle]
pub extern fn bigint_str2errno(cstr_ptr: *const c_char) -> i8 {
    bignum_str2errno(cstr_ptr)
}

#[no_mangle]
pub extern fn bigint_errno2str(e: i8) -> *const c_char {
    bignum_errno2str(e)
}

#[no_mangle]
pub extern fn bigdecimal_digits(id: i64) -> u64 {
    if id <= 0 {
        return 0;
    }

    let g = scc2::ebr::Guard::new();
    if let Some(bigdec) = (&*BIGDECIMAL_INDEX).0.peek(&id, &g) {
        bigdec.digits()
    } else {
        0
    }
}

#[no_mangle]
pub extern fn bigdecimal_format(id: i64, notation: i8) -> *const c_char {
    if id <= 0 {
        return stdlib::ptr::null();
    }

    let g = scc2::ebr::Guard::new();
    if let Some(bigdec) = (&*BIGDECIMAL_INDEX).0.peek(&id, &g) {
        let string =
            if notation > 0 {
                bigdec.to_scientific_notation()
            } else if notation < 0 {
                bigdec.to_engineering_notation()
            } else {
                assert_eq!(notation, 0);
                bigdec.to_plain_string()
            };

        let cstring = CString::new(string).unwrap();
        let out = cstring.as_c_str().as_ptr();

        stdlib::mem::forget(cstring);
        return out;
    }
    
    stdlib::ptr::null()
}

#[no_mangle]
pub extern fn bigint_format(id: i64) -> *const c_char {
    if id <= 0 {
        return stdlib::ptr::null();
    }

    let g = scc2::ebr::Guard::new();
    if let Some(bigint) = (&*BIGINT_INDEX).0.peek(&id, &g) {
        let string = bigint.to_string();

        let cstring = CString::new(string).unwrap();
        let out = cstring.as_c_str().as_ptr();

        stdlib::mem::forget(cstring);
        return out;
    }
    
    stdlib::ptr::null()
}

#[no_mangle]
pub extern fn bigint_bits(id: i64) -> u64 {
    if id <= 0 {
        return 0;
    }

    let g = scc2::ebr::Guard::new();
    if let Some(bigint) = (&*BIGINT_INDEX).0.peek(&id, &g) {
        bigint.bits()
    } else {
        0
    }
}

macro_rules! bignum_ffi_fns {
    ($fn_prefix:ident, $num_name:ident, $num_index:ident) => {
        concat_idents! (num_default = $fn_prefix, _default {
            #[no_mangle]
            pub extern fn num_default() -> i64 {
                let id =
                    match ID::$num_name.default() {
                        Some(v) => v,
                        _ => {
                            return Errno::INT64_ID_EXHAUSTED.to_i64();
                        }
                    };

                let bn = Arc::new($num_name::default());

                let g = scc2::ebr::Guard::new();
                if let Some(entry) = (&*$num_index).1.get(&bn) {
                    return *(entry.get());
                }
                stdlib::mem::drop(g);

                let _ = (&*$num_index).0.entry(id).or_insert_with(|| {
                    (&*$num_index).1.insert(bn.clone(), id).unwrap();
                    bn
                });

                id
            }
        });

        concat_idents! (num_zero = $fn_prefix, _zero {
            #[no_mangle]
            pub extern fn num_zero() -> i64 {
                let bn = Arc::new($num_name::zero());

                let g = scc2::ebr::Guard::new();
                if let Some(entry) = (&*$num_index).1.get(&bn) {
                    return *(entry.get());
                }
                stdlib::mem::drop(g);

                let id =
                    match ID::$num_name.new() {
                        Some(v) => v,
                        _ => {
                            return Errno::INT64_ID_EXHAUSTED.to_i64();
                        }
                    };

                let _ = (&*$num_index).0.entry(id).or_insert_with(|| {
                    (&*$num_index).1.insert(bn.clone(), id).unwrap();
                    bn
                });

                id
            }
        });

        concat_idents! (num_one = $fn_prefix, _one {
            #[no_mangle]
            pub extern fn num_one() -> i64 {
                let bn = Arc::new($num_name::one());

                let g = scc2::ebr::Guard::new();
                if let Some(entry) = (&*$num_index).1.get(&bn) {
                    return *(entry.get());
                }
                stdlib::mem::drop(g);

                let id =
                    match ID::$num_name.new() {
                        Some(v) => v,
                        _ => {
                            return Errno::INT64_ID_EXHAUSTED.to_i64();
                        }
                    };

                let _ = (&*$num_index).0.entry(id).or_insert_with(|| {
                    (&*$num_index).1.insert(bn.clone(), id).unwrap();
                    bn
                });

                id
            }
        });

        concat_idents! (num_drop = $fn_prefix, _drop {
            #[no_mangle]
            pub extern fn num_drop(id: i64) -> i8 {
                if let Some(entry) = (&*$num_index).0.get(&id) {
                    let bn = entry.get().clone();
                    entry.remove_entry();
                    (&*$num_index).1.remove(&bn);
                    Errno::NO_ERROR.to_i8()
                } else {
                    Errno::INT64_ID1_NOT_FOUND.to_i8()
                }
            }
        });

        concat_idents! (num_from_str = $fn_prefix, _from_str {
            #[no_mangle]
            pub extern fn num_from_str(cstr_ptr: *const c_char, radix: u8) -> i64 {
                if radix < 2 || radix > 36 {
                    eprintln!("Error initialize BigDecimal/BigInt: invalid radix! it must be 2~36 (contains 2 and 36)");
                    return Errno::INVALID_RADIX.to_i64();
                }

                if radix != 10 {
                    eprintln!("Currently upstream library (bigdecimal) does not supports from string with radix other than 10. please convert your hex, octect, or binary numbers to radix 10 (decimal) before passing to here.");
                    return Errno::INVALID_RADIX.to_i64();
                }

                let cstr = unsafe { CStr::from_ptr(cstr_ptr) };
                let bignum =
                    match $num_name::parse_bytes(cstr.to_bytes(), radix as u32) {
                        Some(v) => v,
                        _ => {
                            eprintln!("Error initialize BigDecimal/BigInt from string ({cstr:?}) and radix ({radix})!");
                            return Errno::INVALID_STRING.to_i64();
                        }
                    };
                let bignum = Arc::new(bignum);

                let g = scc2::ebr::Guard::new();
                if let Some(id) = (&*$num_index).1.peek(&bignum, &g) {
                    return *id;
                }
                stdlib::mem::drop(g);

                let id =
                    match ID::$num_name.new() {
                        Some(v) => v,
                        _ => {
                            return Errno::INT64_ID_EXHAUSTED.to_i64();
                        }
                    };
                (&*$num_index).0.insert(id, bignum.clone()).unwrap();
                (&*$num_index).1.insert(bignum, id).unwrap();
                id
            }
        });

        concat_idents! (num_eq = $fn_prefix, _eq {
            #[no_mangle]
            pub extern fn num_eq(x_id: i64, y_id: i64) -> i8 {
                if x_id <= 0 {
                    return Errno::INT64_ID1_NOT_FOUND.to_i8();
                }
                if y_id <= 0 {
                    return Errno::INT64_ID2_NOT_FOUND.to_i8();
                }

                if x_id == y_id {
                    return 1;
                }

                let g = scc2::ebr::Guard::new();
                if let Some(x) = (&*$num_index).0.peek(&x_id, &g) {
                    if let Some(y) = (&*$num_index).0.peek(&y_id, &g) {
                        if x == y {
                            1
                        } else {
                            0
                        }
                    } else {
                        Errno::INT64_ID2_NOT_FOUND.to_i8()
                    }
                } else {
                    Errno::INT64_ID1_NOT_FOUND.to_i8()
                }
            }
        });

        concat_idents! (num_lt = $fn_prefix, _lt {
            #[no_mangle]
            pub extern fn num_lt(x_id: i64, y_id: i64) -> i8 {
                if x_id <= 0 {
                    return Errno::INT64_ID1_NOT_FOUND.to_i8();
                }
                if y_id <= 0 {
                    return Errno::INT64_ID2_NOT_FOUND.to_i8();
                }

                if x_id == y_id {
                    return 0;
                }

                let g = scc2::ebr::Guard::new();
                if let Some(x) = (&*$num_index).0.peek(&x_id, &g) {

                    if let Some(y) = (&*$num_index).0.peek(&y_id, &g) {

                        if x < y {
                            1
                        } else {
                            0
                        }
                    } else {
                        Errno::INT64_ID2_NOT_FOUND.to_i8()
                    }
                } else {
                    Errno::INT64_ID1_NOT_FOUND.to_i8()
                }
            }
        });

        concat_idents! (num_gt = $fn_prefix, _gt {
            #[no_mangle]
            pub extern fn num_gt(x_id: i64, y_id: i64) -> i8 {
                if x_id <= 0 {
                    return Errno::INT64_ID1_NOT_FOUND.to_i8();
                }
                if y_id <= 0 {
                    return Errno::INT64_ID2_NOT_FOUND.to_i8();
                }

                if x_id == y_id {
                    return 0;
                }

                let g = scc2::ebr::Guard::new();
                if let Some(x) = (&*$num_index).0.peek(&x_id, &g) {

                    if let Some(y) = (&*$num_index).0.peek(&y_id, &g) {

                        if x > y {
                            1
                        } else {
                            0
                        }
                    } else {
                        Errno::INT64_ID2_NOT_FOUND.to_i8()
                    }
                } else {
                    Errno::INT64_ID1_NOT_FOUND.to_i8()
                }
            }
        });
    }
}
bignum_ffi_fns!(bigdecimal, BigDecimal, BIGDECIMAL_INDEX);
bignum_ffi_fns!(bigint, BigInt, BIGINT_INDEX);

fn bigint_from_bytes(big_endian: bool, sign: i8, bytes_ptr: *const u8, bytes_len: usize, index: bool) -> (i64, Option<BigInt>) {
    let sign =
        if sign < 0 {
            Sign::Minus
        } else if sign > 0 {
            Sign::Plus
        } else {
            assert_eq!(sign, 0);
            Sign::NoSign
        };
    let bytes = unsafe { stdlib::slice::from_raw_parts(bytes_ptr, bytes_len) };

    let bigint =
        if big_endian {
            BigInt::from_bytes_be(sign, bytes)
        } else {
            BigInt::from_bytes_le(sign, bytes)
        };

    if ! index {
        return (Errno::NO_ERROR.to_i64(), Some(bigint));
    }

    let bigint = Arc::new(bigint);

    let g = scc2::ebr::Guard::new();
    if let Some(id) = (&*BIGINT_INDEX).1.peek(&bigint, &g) {
        return (*id, None);
    }

    let id =
        match ID::BigInt.new() {
            Some(v) => v,
            _ => {
                return (Errno::INT64_ID_EXHAUSTED.to_i64(), None);
            }
        };

    (&*BIGINT_INDEX).0.insert(id, bigint.clone()).unwrap();
    (&*BIGINT_INDEX).1.insert(bigint, id).unwrap();

    (id, None)
}

#[no_mangle]
pub extern fn bigint_from_bytes_be(sign: i8, bytes_ptr: *const u8, bytes_len: usize) -> i64 {
    bigint_from_bytes(true, sign, bytes_ptr, bytes_len, true).0
}

#[no_mangle]
pub extern fn bigint_from_bytes_le(sign: i8, bytes_ptr: *const u8, bytes_len: usize) -> i64 {
    bigint_from_bytes(false, sign, bytes_ptr, bytes_len, true).0
}

fn bigdecimal_from_bytes(big_endian: bool, sign: i8, bytes_ptr: *const u8, bytes_len: usize, scale: i64) -> i64 {
    let bigint = bigint_from_bytes(big_endian, sign, bytes_ptr, bytes_len, false).1.unwrap();

    let bigdec = BigDecimal::from_bigint(bigint, scale).normalized();
    let bigdec = Arc::new(bigdec);

    let g = scc2::ebr::Guard::new();
    if let Some(id) = (&*BIGDECIMAL_INDEX).1.peek(&bigdec, &g) {
        return *id;
    }

    let id =
        match ID::BigDecimal.new() {
            Some(v) => v,
            _ => {
                return Errno::INT64_ID_EXHAUSTED.to_i64();
            }
        };

    (&*BIGDECIMAL_INDEX).0.insert(id, bigdec.clone()).unwrap();
    (&*BIGDECIMAL_INDEX).1.insert(bigdec, id).unwrap();

    id
}

#[no_mangle]
pub extern fn bigdecimal_from_bytes_be(sign: i8, bytes_ptr: *const u8, bytes_len: usize, scale: i64) -> i64 {
    bigdecimal_from_bytes(true, sign, bytes_ptr, bytes_len, scale)
}

#[no_mangle]
pub extern fn bigdecimal_from_bytes_le(sign: i8, bytes_ptr: *const u8, bytes_len: usize, scale: i64) -> i64 {
    bigdecimal_from_bytes(false, sign, bytes_ptr, bytes_len, scale)
}

macro_rules! bignum_ffi_fn_from_ints {
    ($fn_prefix:ident, $num_name:ident, $num_index:ident, $($int:ident)*) => {$(
        concat_idents! (num_from_int = $fn_prefix, _from_, $int {
            #[no_mangle]
            pub extern fn num_from_int(i: $int) -> i64 {
                let bignum = Arc::new($num_name::from(i));

                let g = scc2::ebr::Guard::new();
                if let Some(id) = (&*$num_index).1.peek(&bignum, &g) {
                    return *id;
                }
                stdlib::mem::drop(g);

                let id =
                    match ID::$num_name.new() {
                        Some(v) => v,
                        _ => {
                            return Errno::INT64_ID_EXHAUSTED.to_i64();
                        }
                    };
                (&*$num_index).0.insert(id, bignum.clone()).unwrap();
                (&*$num_index).1.insert(bignum, id).unwrap();
                id
            }
        });
    )*};
}
bignum_ffi_fn_from_ints!(bigdecimal, BigDecimal, BIGDECIMAL_INDEX, u8 u16 u32 u64 u128 i8 i16 i32 i64 i128);
bignum_ffi_fn_from_ints!(bigint, BigInt, BIGINT_INDEX, u8 u16 u32 u64 u128 i8 i16 i32 i64 i128);

#[no_mangle]
pub extern fn bigdecimal_from_usize(i: usize) -> i64 {
    bigdecimal_from_u128(i as u128)
}

#[no_mangle]
pub extern fn bigdecimal_from_isize(i: isize) -> i64 {
    bigdecimal_from_i128(i as i128)
}

#[no_mangle]
pub extern fn bigint_from_usize(i: usize) -> i64 {
    bigint_from_u128(i as u128)
}

#[no_mangle]
pub extern fn bigint_from_isize(i: isize) -> i64 {
    bigint_from_i128(i as i128)
}

macro_rules! bignum_ffi_fn_ops_1 {
    ($num_name:ident, $num_index:ident, $fn_name:ident, $op_method:ident) => {
        #[no_mangle]
        pub extern fn $fn_name(id: i64) -> i64 {
            if id <= 0 {
                return Errno::INT64_ID1_NOT_FOUND.to_i64();
            }

            let g = scc2::ebr::Guard::new();
            if let Some(bn) = (&*$num_index).0.peek(&id, &g) {
                use stdlib::any::Any;

                let mut any_res: Box<dyn Any> = Box::new(bn.$op_method());
                let res =
                    if let Some(maybe_res) = any_res.downcast_mut::<Option<$num_name>>() {
                        match maybe_res.take() {
                            Some(v) => {
                                Arc::new(v)
                            },
                            _ => {
                                return Errno::NO_ERROR.to_i64();
                            }
                        }
                    } else {
                        any_res.downcast::<$num_name>().unwrap().into()
                    };

                if let Some(id) = (&*$num_index).1.peek(&res, &g) {
                    return *id;
                }


                let id =
                    match ID::$num_name.new() {
                        Some(v) => v,
                        _ => {
                            return Errno::INT64_ID_EXHAUSTED.to_i64();
                        }
                    };

                (&*$num_index).0.insert(id, res.clone()).unwrap();
                (&*$num_index).1.insert(res, id).unwrap();

                id
            } else {
                Errno::INT64_ID1_NOT_FOUND.to_i64()
            }
        }
    }
}

macro_rules! bigdecimal_ffi_fn_ops_1 {
    ($fn_name:ident, $op_method:ident) => {
        bignum_ffi_fn_ops_1!(BigDecimal, BIGDECIMAL_INDEX, $fn_name, $op_method);
    }
}
bigdecimal_ffi_fn_ops_1!(bigdecimal_abs, abs);
bigdecimal_ffi_fn_ops_1!(bigdecimal_sqrt, sqrt);
bigdecimal_ffi_fn_ops_1!(bigdecimal_cbrt, cbrt);
bigdecimal_ffi_fn_ops_1!(bigdecimal_ln, ln);
bigdecimal_ffi_fn_ops_1!(bigdecimal_exp, exp);
bigdecimal_ffi_fn_ops_1!(bigdecimal_half, half);
bigdecimal_ffi_fn_ops_1!(bigdecimal_cube, cube);

macro_rules! bigint_ffi_fn_ops_1 {
    ($fn_name:ident, $op_method:ident) => {
        bignum_ffi_fn_ops_1!(BigInt, BIGINT_INDEX, $fn_name, $op_method);
    }
}
bigint_ffi_fn_ops_1!(bigint_abs, abs);
bigint_ffi_fn_ops_1!(bigint_sqrt, sqrt);
bigint_ffi_fn_ops_1!(bigint_cbrt, cbrt);

macro_rules! bignum_ffi_fn_ops_2 {
    ($num_name:ident, $num_index:ident, $fn_name:ident, $op_trait:ty, $op_method:ident) => {
        #[no_mangle]
        pub extern fn $fn_name(x_id: i64, y_id: i64) -> i64 {
            if x_id <= 0 {
                return Errno::INT64_ID1_NOT_FOUND.to_i64();
            }
            if y_id <= 0 {
                return Errno::INT64_ID2_NOT_FOUND.to_i64();
            }

            let g = scc2::ebr::Guard::new();
            if let Some(x) = (&*$num_index).0.peek(&x_id, &g) {
                if let Some(y) = (&*$num_index).0.peek(&y_id, &g) {

                    const OP_METHOD: &'static str = stringify!($op_method);
                    match OP_METHOD {
                        "div" | "rem" => {
                            if y.is_zero() {
                                return Errno::DIVISION_BY_ZERO.to_i64();
                            }
                        },
                        _ => {}
                    }

                    use $op_trait;
                    let z = (&**x).$op_method(&**y);
                    let z = Arc::new(z);

                    if let Some(id) = (&*$num_index).1.peek(&z, &g) {
                        return *id;
                    }
                    stdlib::mem::drop(g);

                    let z_id =
                        match ID::$num_name.new() {
                            Some(v) => v,
                            _ => {
                                return Errno::INT64_ID_EXHAUSTED.to_i64();
                            }
                        };

                    (&*$num_index).0.insert(z_id, z.clone()).unwrap();
                    (&*$num_index).1.insert(z, z_id).unwrap();

                    z_id
                } else {
                    Errno::INT64_ID2_NOT_FOUND.to_i64()
                }
            } else {
                Errno::INT64_ID1_NOT_FOUND.to_i64()
            }
        }
    };
}

macro_rules! bigdecimal_ffi_fn_ops_2 {
    ($fn_name:ident, $op_trait:ty, $op_method:ident) => {
        bignum_ffi_fn_ops_2!(BigDecimal, BIGDECIMAL_INDEX, $fn_name, $op_trait, $op_method);
    }
}
bigdecimal_ffi_fn_ops_2!(bigdecimal_add, Add, add);
bigdecimal_ffi_fn_ops_2!(bigdecimal_sub, Sub, sub);
bigdecimal_ffi_fn_ops_2!(bigdecimal_mul, Mul, mul);
bigdecimal_ffi_fn_ops_2!(bigdecimal_div, Div, div);
bigdecimal_ffi_fn_ops_2!(bigdecimal_rem, Rem, rem);
bigdecimal_ffi_fn_ops_2!(bigdecimal_mod, Rem, rem);
bigdecimal_ffi_fn_ops_2!(bigdecimal_pow, Pow, pow);

macro_rules! bigint_ffi_fn_ops_2 {
    ($fn_name:ident, $op_trait:ty, $op_method:ident) => {
        bignum_ffi_fn_ops_2!(BigInt, BIGINT_INDEX, $fn_name, $op_trait, $op_method);
    }
}
bigint_ffi_fn_ops_2!(bigint_add, Add, add);
bigint_ffi_fn_ops_2!(bigint_sub, Sub, sub);
bigint_ffi_fn_ops_2!(bigint_mul, Mul, mul);
bigint_ffi_fn_ops_2!(bigint_div, Div, div);
bigint_ffi_fn_ops_2!(bigint_rem, Rem, rem);
bigint_ffi_fn_ops_2!(bigint_mod, Rem, rem);
//bigint_ffi_fn_ops_2!(bigint_pow, num_traits::Pow, pow);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let x = bigdecimal_from_str(CString::new(String::from("1.23")).unwrap().as_c_str().as_ptr(), 10);
        println!("x id = {x}");

        let xf = bigdecimal_format(x, 0);
        println!("x format ptr = {xf:?}");
        println!("x format = {:?}", unsafe { CStr::from_ptr(xf) });
    }
}
