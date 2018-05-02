// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#include <stdarg.h>
#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

typedef enum {
    TAG_DOUBLE,
    TAG_LONG,
    TAG_SHORT,
    TAG_BYTE,
    TAG_CSTR,
    TAG_SKIP,
} tag;

typedef struct {
    tag answer_type;
    union {
        double double_precision;
        int64_t num_long;
        int16_t num_short;
        int8_t byte;
        char* cstr;
        tag skip_ty;
    } answer_data;
} answer;

#define MK_DOUBLE(n) \
    { TAG_DOUBLE, { .double_precision = n } }
#define MK_LONG(n) \
    { TAG_LONG, { .num_long = n } }
#define MK_SHORT(n) \
    { TAG_SHORT, { .num_short = n } }
#define MK_BYTE(b) \
    { TAG_BYTE, { .byte = b } }
#define MK_CSTR(s) \
    { TAG_CSTR, { .cstr = s } }
#define MK_SKIP(ty) \
    { TAG_SKIP, { .skip_ty = TAG_ ## ty } }

extern size_t check_rust(size_t argc, const answer* answers, va_list ap);
extern size_t check_rust_copy(size_t argc, const answer* answers, va_list ap);

size_t test_check_rust(size_t argc, const answer* answers, ...) {
    size_t ret = 0;
    va_list ap;
    va_start(ap, answers);
    ret = check_rust(argc, answers, ap);
    va_end(ap);
    return ret;
}

size_t test_check_rust_copy(size_t argc, const answer* answers, ...) {
    size_t ret = 0;
    va_list ap;
    va_start(ap, answers);
    ret = check_rust_copy(argc, answers, ap);
    va_end(ap);
    return ret;
}

int main(int argc, char* argv[]) {
    answer answers0[] = {MK_DOUBLE(3.14), MK_BYTE('a'), MK_DOUBLE(6.28),
                         MK_SHORT(42), MK_LONG(12l), MK_CSTR("Hello, World!")};
    assert(test_check_rust(4, answers0, 3.14, 'a', 6.28, 42, 12l,
                           "Hello, World!") == 0);

    answer answers1[] = { MK_SKIP(DOUBLE), MK_SKIP(SHORT), MK_SKIP(BYTE),
                          MK_SKIP(CSTR), MK_CSTR("Correctly skipped and copied list") };
    assert(test_check_rust_copy(5, answers1, 6.28, 16, 'A', "Skip Me!",
                                "Correctly skipped and copied list") == 0);
    return 0;
}
