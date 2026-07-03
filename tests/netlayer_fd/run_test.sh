#!/bin/bash
set -e

rm -f /tmp/a2b /tmp/b2a
mkfifo /tmp/a2b /tmp/b2a

echo "Starting Node B..."
stdbuf -o0 cargo run --no-default-features -- tests/netlayer_fd/node_b.pr < /tmp/a2b > /tmp/b2a &
PID_B=$!

echo "Starting Node A..."
stdbuf -o0 cargo run --no-default-features -- tests/netlayer_fd/node_a.pr < /tmp/b2a > /tmp/a2b &
PID_A=$!

wait $PID_A
echo "Node A exited."

wait $PID_B
echo "Node B exited."

rm -f /tmp/a2b /tmp/b2a
echo "Done."
