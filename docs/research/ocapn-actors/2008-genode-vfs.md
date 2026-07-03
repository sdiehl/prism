# Genode VFS Networking

Genode is a capability-based operating-system framework. Its architecture emphasizes component-based composition and fine-grained security through capabilities. Networking in Genode is integrated via its Virtual File System (VFS) subsystem, exposing network interfaces and services as file-like objects.

## Key Concepts

*   **Capability-Based Security**: Access to network resources (NICs, sockets) is mediated by capabilities, ensuring that only authorized components can interact with the network.
*   **VFS Integration**: Network stacks and services are implemented as plugins within Genode's VFS (e.g., `vfs_lxip.lib.so` or `vfs_lwip.lib.so`). This allows network resources to be accessed using a unified, file-oriented interface. For example, a TCP/IP stack might expose sockets as files within a specific VFS path.
*   **Component Composition**: Genode's design allows developers to assemble network functionality by combining different VFS components. This could include:
    *   **NIC drivers**: Exposed as devices in the VFS.
    *   **Network stacks**: Higher-level VFS plugins (e.g., lwIP, custom stacks) that provide TCP/IP, UDP, etc.
    *   **Socket APIs**: The VFS interfaces that allow user-space components to open, read, write, and control network sockets.

## Relevant API Signatures

Genode's VFS networking is split into two layers of APIs:
1.  **The VFS Directory Protocol / Path API**: How sockets are represented dynamically in the virtual filesystem namespace.
2.  **The C++ VFS Plugin API (`Genode::Vfs`)**: The C++ interfaces and signatures that backing plugins implement to handle open, close, read, write, and watch events.

### 1. VFS Directory Protocol & Path API

In Genode, network stacks are instantiated in the VFS config (e.g., routing DHCP configuration to the plugin):
```xml
<vfs>
  <dir name="socket">
    <lxip dhcp="yes"/>
  </dir>
</vfs>
```

This exposes a directory structure at `/socket`:
```
/socket/tcp/
/socket/tcp/new_socket
/socket/udp/
/socket/udp/new_socket
/socket/address      (ASCII reflecting current IP)
/socket/netmask      (ASCII subnet mask)
/socket/gateway      (ASCII default gateway)
/socket/nameserver   (ASCII DNS resolver)
```

To interact with sockets without a standard BSD library, a component performs the following filesystem-oriented operations:

#### Socket Creation
*   **TCP/UDP**: Open `/socket/tcp/new_socket` (or `udp`) and read the returned ASCII content. The stack creates a dynamic subdirectory named after the socket ID (e.g., `/socket/tcp/1/`) containing:
    ```
    /socket/tcp/1/bind
    /socket/tcp/1/connect
    /socket/tcp/1/data
    /socket/tcp/1/local
    /socket/tcp/1/remote
    /socket/tcp/1/listen         (for server sockets)
    /socket/tcp/1/accept         (reads "1" or nothing indicating queued connection)
    /socket/tcp/1/accept_socket  (opened to accept a queued client socket)
    ```

#### Socket Control and Data Transfer
*   **Bind**: Write an IP and port (e.g., `0.0.0.0:80`) into `/socket/tcp/1/bind`.
*   **Connect**: Write the target address (e.g., `88.198.56.169:443`) into `/socket/tcp/1/connect`.
*   **Send/Receive**: Read from and write to `/socket/tcp/1/data`.
*   **Close**: Unlink (delete) the socket directory `/socket/tcp/1/`.

---

### 2. C++ VFS Plugin API (`Genode::Vfs`)

Under the hood, VFS plugins like `vfs_lxip` implement the `Directory_service` and `File_io_service` abstract classes.

#### Directory Service Interface (`vfs/directory_service.h`)
The plugin implements these methods to translate path operations (like opening or deleting sockets) into network actions:

```cpp
struct Genode::Vfs::Directory_service : Interface
{
    // Opens files under /socket (e.g., 'new_socket', 'connect', 'data')
    virtual Open_result open(char const  *path,
                             unsigned     mode,
                             Vfs_handle **handle,
                             Allocator   &alloc) = 0;

    // Destroys/closes a VFS socket handle
    virtual void close(Vfs_handle *handle) = 0;

    // Triggered to close/destroy a socket by unlinking its directory
    virtual Unlink_result unlink(char const *path) = 0;

    // Reads socket directory entries
    virtual file_size num_dirent(char const *path) = 0;
};
```

#### File I/O Service Interface (`vfs/file_io_service.h`)
Once a handle is obtained (e.g., to `/socket/tcp/1/data`), read and write operations are routed here:

```cpp
struct Genode::Vfs::File_io_service : Interface
{
    // Write data to transmit payload, or write to control files ('bind', 'connect')
    virtual Write_result write(Vfs_handle *vfs_handle,
                               Const_byte_range_ptr const &src,
                               size_t &out_count) = 0;

    // Queue read operations on 'data' or control/config files
    virtual bool queue_read(Vfs_handle *vfs_handle, size_t count) { return true; }

    // Retrieve data read from the underlying network buffers
    virtual Read_result complete_read(Vfs_handle *vfs_handle,
                                      Byte_range_ptr const &dst,
                                      size_t &out_count) = 0;

    // Polling interfaces for non-blocking I/O
    virtual bool read_ready(Vfs_handle const &vfs_handle) const = 0;
    virtual bool write_ready(Vfs_handle const &vfs_handle) const = 0;
    virtual bool notify_read_ready(Vfs_handle *vfs_handle) { return true; }
};
```

#### Libc Mapping
For POSIX-compatible code, Genode's C runtime (`libc`) maps BSD calls directly to these VFS actions via the `<libc socket="/socket"/>` directive:
*   `socket()` -> Open `/socket/tcp/new_socket`, read directory ID, then open `data`.
*   `connect(fd, addr)` -> Write ASCII representation of `addr` to `/socket/tcp/<id>/connect`.
*   `send(fd, buf)` -> Write to `/socket/tcp/<id>/data`.
*   `close(fd)` -> Unlink `/socket/tcp/<id>/`.

## Relationship to Netlayers

Genode's approach to networking is highly relevant to the concept of a secure and abstract netlayer:

*   **Resource Abstraction**: The VFS provides a consistent, capability-protected interface to network resources, abstracting away hardware details.
*   **Security Enforcement**: By treating network access as file access within the VFS, Genode ensures that capabilities are the primary mechanism for controlling network access. This aligns with the goal of capability-based networking.
*   **Composability**: The plugin-based VFS architecture makes it easy to integrate different network protocols or services, similar to how netlayers abstract over different transport protocols.

## Lessons for Prism

1.  **Unified Resource Model**: Modeling network access as part of a broader VFS framework, secured by capabilities, provides a consistent abstraction.
2.  **Capability-Driven Networking**: Genode demonstrates that network access can be securely managed by passing explicit capabilities for network interfaces and services.
3.  **Component-Based Networking**: The ability to compose network functionality from smaller, reusable VFS components aligns with modern system design principles.

## Resources

*   [Genode Operating System Documentation](https://genode.org/documentation/)
*   [Genodians Blog - VFS Networking](https://genodians.org/nfeske/2020-09-03-vfs-networking)
*   [Genodians Blog - VFS Networking Part 3](https://genodians.org/m-stein/2021-09-23-vfs-3)
*   [Genode 17.02 Release Notes - VFS lxip plugin](https://genode.org/documentation/release-notes/17.02)
