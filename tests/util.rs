/* Copyright 2017 Jordan Miner
 *
 * Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
 * http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
 * <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
 * option. This file may not be copied, modified, or distributed
 * except according to those terms.
 */

extern crate avro;
extern crate hyper;

use std::fs::{self, File};
use std::io::{self, BufReader, BufWriter};
use std::path::Path;

pub fn download_avro_jar_if_needed() -> Result<(), ()> {
    let avro_jar_size = 1_555_202;
    let url = "http://archive.apache.org/dist/avro/avro-1.8.2/java/avro-1.8.2.jar";

    fs::create_dir_all("tests/avro").expect("failed to create tests/avro");
    if Path::new("tests/avro/avro.jar").exists() {
        let jar_metadata = fs::metadata("tests/avro/avro.jar")
            .expect("could not get avro.jar metadata");
        if jar_metadata.len() == avro_jar_size {
            return Ok(());
        }
        println!("avro.jar size doesn't match: {} vs {}", jar_metadata.len(), avro_jar_size);
    }
    println!("downloading avro.jar");

    let client = hyper::Client::new();
    let mut response = client.get(url).send().unwrap();
    if response.status != hyper::Ok {
        println!("failed to download the Avro jar file from {}: {}", url, response.status);
        return Err(());
    }
    let mut reader = BufReader::with_capacity(16 * 1024, &mut response);

    let mut output = match File::create("tests/avro/avro.jar") {
        Ok(f) => f,
        Err(err) => {
            println!("failed to create output avro.jar file: {}", err);
            return Err(());
        }
    };
    let mut writer = BufWriter::new(&mut output);
    if let Err(err) = io::copy(&mut reader, &mut writer) {
        println!("failed to download the Avro jar file from {}: {}", url, err);
        return Err(());
    }

    Ok(())
}
