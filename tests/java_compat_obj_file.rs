/* Copyright 2017 Jordan Miner
 *
 * Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
 * http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
 * <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
 * option. This file may not be copied, modified, or distributed
 * except according to those terms.
 */

extern crate avro;

mod util;

#[cfg_attr(not(feature = "java-compat"), ignore)]
#[test]
fn test_java_compat_obj_file() {
    util::download_avro_jar_if_needed().unwrap();
}
