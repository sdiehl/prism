use std::io::BufReader;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::thread;

#[test]
fn test_fd_netlayer() {
    let (mut a_write, mut b_write) = UnixStream::pair().unwrap();
    let mut a_read = BufReader::new(a_write.try_clone().unwrap());
    let mut b_read = BufReader::new(b_write.try_clone().unwrap());

    let node_a_src = prism::with_prelude(include_str!("netlayer_fd/node_a.pr"));

    let node_b_src = prism::with_prelude(include_str!("netlayer_fd/node_b.pr"));

    let handle = thread::spawn(move || {
        println!("Node B thread started.");
        let r = prism::interpret_io_at(&node_b_src, Path::new("."), &mut b_write, &mut b_read);
        println!("Node B thread finished with: {:?}", r);
    });

    println!("Node A started.");
    let r = prism::interpret_io_at(&node_a_src, Path::new("."), &mut a_write, &mut a_read);
    println!("Node A finished with: {:?}", r);

    handle.join().unwrap();
}
