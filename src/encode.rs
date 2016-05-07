/* Copyright 2016 Jordan Miner
 *
 * Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
 * http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
 * <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
 * option. This file may not be copied, modified, or distributed
 * except according to those terms.
 */

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
