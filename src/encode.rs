/* Copyright 2016 Jordan Miner
 *
 * Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
 * http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
 * <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
 * option. This file may not be copied, modified, or distributed
 * except according to those terms.
 */

use std::io;
use std::io::Write;

#[derive(Debug)]
pub enum EncodeErrorKind {
    WriteFailed(io::Error),
}

#[derive(Debug)]
pub struct EncodeError {
    pub kind: EncodeErrorKind,
}

impl From<io::Error> for EncodeError {
    fn from(err: io::Error) -> EncodeError {
        EncodeError { kind: EncodeErrorKind::WriteFailed(err) }
    }
}

pub fn encode_var_len_u64<W: Write>(writer: &mut W, mut num: u64) -> Result<(), EncodeError> {
    loop {
        let mut b = (num & 0b0111_1111) as u8;
        num >>= 7;
        if num == 0 {
            try!(writer.write(&[b]));
            break;
        }
        b |= 0b1000_0000;
        try!(writer.write(&[b]));
    }
    Ok(())
}

#[test]
fn test_encode_var_len_u64() {
    let mut vec = vec![];

    encode_var_len_u64(&mut vec, 3).unwrap();
    assert_eq!(&vec, &b"\x03");
    vec.clear();

    encode_var_len_u64(&mut vec, 128).unwrap();
    assert_eq!(&vec, &b"\x80\x01");
    vec.clear();

    encode_var_len_u64(&mut vec, 130).unwrap();
    assert_eq!(&vec, &b"\x82\x01");
    vec.clear();

    encode_var_len_u64(&mut vec, 944261).unwrap();
    assert_eq!(&vec, &b"\x85\xD1\x39");
    vec.clear();
}

pub fn encode_zig_zag(num: i64) -> u64 {
    // compiles to (num << 1) ^ (num >> 63)
    if num < 0 {
        !((num as u64) << 1)
    } else {
        (num as u64) << 1
    }
}

#[test]
fn test_encode_zig_zag() {
    assert_eq!(encode_zig_zag(0), 0);
    assert_eq!(encode_zig_zag(-1), 1);
    assert_eq!(encode_zig_zag(1), 2);
    assert_eq!(encode_zig_zag(-2), 3);
    assert_eq!(encode_zig_zag(i64::min_value()), 0xFFFFFFFF_FFFFFFFF);
    assert_eq!(encode_zig_zag(i64::max_value()), 0xFFFFFFFF_FFFFFFFE); // 0x7FFF...FF
}
