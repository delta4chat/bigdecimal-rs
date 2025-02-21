#!/bin/env python3

import ctypes

LIBRARY_PATH = "./target/release/libbigdecimal.so"

def open_lib():
    LIBRARY_CACHE = {}

    def _open_lib(libpath=None):
        if not libpath:
            libpath = LIBRARY_PATH

        if libpath in LIBRARY_CACHE:
            return LIBRARY_CACHE[libpath]
        
        cdll = ctypes.CDLL(libpath)
        LIBRARY_CACHE[libpath] = cdll
        return cdll

    return _open_lib
open_lib = open_lib()

bigint = (2**64).__class__

class BigDecimalRustError(Exception):
    pass

drops = []

class BigDecimalRust:
    def __init__(self, *args):
        lib = open_lib(LIBRARY_PATH)
        for name in ("default", "zero", "one", "abs", "sqrt", "cbrt", "ln", "exp", "eq", "add", "sub", "mul", "pow", "div", "rem", "mod", "digits", "format", "from_str", "errno2str", "str2errno", "drop"):
            func = getattr(lib, "bigdecimal_"+name)
            if name == 'digits':
                func.restype = ctypes.c_uint64
            elif name in ("format", "errno2str"):
                func.restype = ctypes.c_char_p
            elif name in ("str2errno", "drop", "eq"):
                func.restype = ctypes.c_int8
            else:
                func.restype = ctypes.c_int64

        if len(args) >= 1:
            num = args[0]

            if isinstance(num, self.__class__):
                self._lib = num._lib
                self._handle = num._handle
                self._notation = num._notation
                return

            if num.__class__ in (str, bytes):
                pass
            elif num.__class__ in (int, bigint):
                num = str(num)
            else:
                raise TypeError("does not know how to convert num to ASCII string")

            if num.__class__ is not bytes:
                num = num.encode("ascii")

            radix = 10
            if len(args) >= 2:
                radix = int(args[1])
            radix = ctypes.c_int8(radix)

            handle = lib.bigdecimal_from_str(num, radix)

            if handle <= 0:
                msg = lib.bigdecimal_errno2str(ctypes.c_int8(handle))
                raise BigDecimalRustError(handle, msg)

            handle = ctypes.c_int64(handle)
        else:
            # lazy initialized
            handle = None

        self._lib = lib
        self._handle = handle
        self._notation = ctypes.c_int8(0)

    def _lazy(self):
        if self._handle is not None:
            return

        handle = self._lib.bigdecimal_default()
        if handle <= 0:
            msg = self._lib.bigdecimal_errno2str(ctypes.c_int8(handle))
            raise BigDecimalRustError(handle, msg)

        self._handle = ctypes.c_int64(handle)

    def __eq__(self, other):
        self._lazy()

        if not isinstance(other, self.__class__):
            other = self.__class__(other)

        other._lazy()

        if self._handle == other._handle:
            return True

        result = self._lib.bigdecimal_eq(self._handle, other._handle)
        if result < 0:
            msg = self._lib.bigdecimal_errno2str(ctypes.c_int8(result))
            raise BigDecimalRustError(result, msg)

        if result:
            return True
        else:
            return False

    def digits(self):
        self._lazy()
        return self._lib.bigdecimal_digits(self._handle)

    def set_notation(self, notation):
        notation = int(notation)
        assert notation >= -128 and notation <= 127

        self._notation = ctypes.c_int8(notation)
        return self

    def ln(self):
        self._lazy()

        handle = self._lib.bigdecimal_ln(self._handle)
        if handle <= 0:
            msg = self._lib.bigdecimal_errno2str(ctypes.c_int8(handle))
            raise BigDecimalRustError(handle, msg)

        result = self.__class__()
        result._handle = ctypes.c_int64(handle)
        return result

    def exp(self):
        self._lazy()

        handle = self._lib.bigdecimal_ln(self._handle)
        if handle <= 0:
            msg = self._lib.bigdecimal_errno2str(ctypes.c_int8(handle))
            raise BigDecimalRustError(handle, msg)

        result = self.__class__()
        result._handle = ctypes.c_int64(handle)
        return result

    def to_string(self):
        self._lazy()

        s = self._lib.bigdecimal_format(self._handle, self._notation)

        if s is None:
            raise BigDecimalRustError(-100, b"unable to format BigDecimal (rust struct)")

        s = s.decode("ascii")
        return s

    def __str__(self):
        if self.digits() < 5000:
            return self.to_plain_string()
        else:
            return self.to_scientific_notation()
    
    def to_plain_string(self):
        return self.copy().set_notation(0).to_string()
    def to_scientific_notation(self):
        return self.copy().set_notation(1).to_string()
    def to_engineering_notation(self):
        return self.copy().set_notation(-1).to_string()

    def copy(self):
        return self.__class__(self)

    def __repr__(self):
        self._lazy()

        return "BigDecimalRust('%s') # handle %s at %s" % (self.__str__(), hex(self._handle.value), hex(id(self)))

    def add(self, other):
        if not isinstance(other, self.__class__):
            other = self.__class__(other)

        self._lazy()

        handle = self._lib.bigdecimal_add(self._handle, other._handle)
        if handle <= 0:
            msg = self._lib.bigdecimal_errno2str(ctypes.c_int8(handle))
            raise BigDecimalRustError(handle, msg)

        result = self.__class__()
        result._handle = ctypes.c_int64(handle)
        return result
    def __add__(self, other):
        return self.add(other)

    def sub(self, other):
        if not isinstance(other, self.__class__):
            other = self.__class__(other)

        self._lazy()

        handle = self._lib.bigdecimal_sub(self._handle, other._handle)
        if handle <= 0:
            msg = self._lib.bigdecimal_errno2str(ctypes.c_int8(handle))
            raise BigDecimalRustError(handle, msg)

        result = self.__class__()
        result._handle = ctypes.c_int64(handle)
        return result
    def __sub__(self, other):
        return self.sub(other)

    def mul(self, other):
        if not isinstance(other, self.__class__):
            other = self.__class__(other)

        self._lazy()

        handle = self._lib.bigdecimal_mul(self._handle, other._handle)
        if handle <= 0:
            msg = self._lib.bigdecimal_errno2str(ctypes.c_int8(handle))
            raise BigDecimalRustError(handle, msg)

        result = self.__class__()
        result._handle = ctypes.c_int64(handle)
        return result
    def __mul__(self, other):
        return self.mul(other)

    def pow(self, other):
        if not isinstance(other, self.__class__):
            other = self.__class__(other)

        self._lazy()

        handle = self._lib.bigdecimal_pow(self._handle, other._handle)
        if handle <= 0:
            msg = self._lib.bigdecimal_errno2str(ctypes.c_int8(handle))
            raise BigDecimalRustError(handle, msg)

        result = self.__class__()
        result._handle = ctypes.c_int64(handle)
        return result

    def __pow__(self, other):
        return self.pow(other)

    def div(self, other):
        if not isinstance(other, self.__class__):
            other = self.__class__(other)

        self._lazy()

        handle = self._lib.bigdecimal_div(self._handle, other._handle)
        if handle <= 0:
            msg = self._lib.bigdecimal_errno2str(ctypes.c_int8(handle))
            if msg == b"DIVISION_BY_ZERO":
                raise \
                        ZeroDivisionError("division by zero")
            raise BigDecimalRustError(handle, msg)

        result = self.__class__()
        result._handle = ctypes.c_int64(handle)
        return result
    def __div__(self, other):
        return self.div(other)
    def __truediv__(self, other):
        return self.div(other)

    def mod(self, other):
        if not isinstance(other, self.__class__):
            other = self.__class__(other)

        self._lazy()

        handle = self._lib.bigdecimal_mod(self._handle, other._handle)
        if handle <= 0:
            msg = self._lib.bigdecimal_errno2str(ctypes.c_int8(handle))
            if msg == b"DIVISION_BY_ZERO":
                raise \
                        ZeroDivisionError("division by zero")
            raise BigDecimalRustError(handle, msg)

        result = self.__class__()
        result._handle = ctypes.c_int64(handle)
        return result

    def __mod__(self, other):
        return self.mod(other)

    def divmod(self, other):
        r = self.mod(other)
        q = (self - r) / other
        return (q, r)
    def __divmod__(self, other):
        return self.divmod(other)

    def __del__(self):
        return
        drops.append(("dropping", self._handle, self._lib.bigdecimal_drop(self._handle)))

import time
def t(f):
    assert callable(f)
    t1 = time.monotonic_ns()
    f()
    t2 = time.monotonic_ns()
    print(t1,t2)
    return BigDecimalRust(t2 - t1) / 1000000000

