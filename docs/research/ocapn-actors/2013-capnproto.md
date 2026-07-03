# Cap'n Proto: The Layered RPC Protocol

Cap'n Proto is a data serialization format and an RPC protocol. Its RPC protocol operates at **Layer 2** (the RPC semantic layer), abstracting away the underlying transport layer (Layer 3, e.g., TCP/IP).

## Key Features Relevant to Netlayers:

*   **Layered Architecture**: Cap'n Proto defines distinct layers for serialization, RPC, and transport. This separation allows RPC to be independent of the specific network transport used.
*   **Promise Pipelining**: Like CapTP, Cap'n Proto supports promise pipelining, allowing clients to send a "pipeline" of messages that refer to results not yet computed. This significantly improves latency in distributed systems.
*   **"Layer 2 Proxy" Concept**: A notable aspect of Cap'n Proto's flexibility is the ability to implement proxies that operate purely at the RPC layer. Such a proxy can connect two RPC endpoints without needing to understand the underlying transport details of each. This is crucial for scenarios like:
    *   **Skipping Layer 3**: A Cap'n Proto proxy can bridge two Layer 4 connections (e.g., raw TCP sockets) by speaking the Cap'n Proto RPC protocol on both sides. This bypasses the need for standard IP routing (Layer 3) in certain network topologies or customized network stacks.
    *   **Transport Agnosticism**: The RPC layer is designed to be pluggable, making it adaptable to various transports.
*   **Time-Travel RPC**: For debugging, Cap'n Proto supports "time-travel RPC," where the entire sequence of RPC calls and responses can be recorded and replayed.

## Relationship to Netlayers

Cap'n Proto's RPC layer provides a robust model for distributed communication that shares many goals with CapTP's netlayer abstraction:

*   **Abstraction over Transport**: Both aim to abstract away the underlying network details.
*   **Efficiency**: Promise pipelining in Cap'n Proto (and CapTP) minimizes latency.
*   **Proxying/Bridging**: The "Layer 2 Proxy" concept demonstrates how RPC protocols can mediate connections, a pattern relevant to building secure netlayers that might bridge different network environments.

## Lessons for Prism:

1.  **Protocol Layering is Key**: Treat the RPC protocol (CapTP) and the transport (Netlayer) as distinct concerns, enabling flexibility in transport choice.
2.  **Leverage Existing RPC Models**: Cap'n Proto's RPC features, especially pipelining and transport abstraction, offer valuable patterns for designing robust distributed systems.
3.  **Proxying for Network Flexibility**: The idea of RPC-level proxies can be explored for building sophisticated netlayers that can adapt to different network conditions or security requirements.

## Resources:

*   [Cap'n Proto RPC Documentation](https://capnproto.org/rpc.html)
*   [Cap'n Proto Other Languages](https://capnproto.org/otherlang.html) ; (Mentions Haskell Cap'n Proto RPC implementation)
*   [zenhack/haskell-capnp](https://github.com/zenhack/haskell-capnp) ; Haskell implementation details
