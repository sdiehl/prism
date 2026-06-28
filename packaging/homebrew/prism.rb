# typed: strict
# frozen_string_literal: true

# Seed copy of the Homebrew formula. The live formula lives in the tap repo
# sdiehl/homebrew-prism at Formula/prism.rb; copy this there once (see
# packaging/homebrew/README.md). The release workflow rewrites url, sha256, and
# version on every tagged release, so after the one-time setup it stays current
# on its own.
class Prism < Formula
  desc "Effect-typed functional language with a call-by-push-value core, via LLVM"
  homepage "https://github.com/sdiehl/prism"
  url "https://github.com/sdiehl/prism/releases/download/v0.3.0/prism-0.3.0-aarch64-apple-darwin.tar.gz"
  version "0.3.0"
  sha256 "0000000000000000000000000000000000000000000000000000000000000000"
  license "MIT"

  # Ships an Apple Silicon binary only for now.
  depends_on arch: :arm64
  # LLVM 22 supplies the z3 and zstd dylibs the binary links, plus the clang it
  # shells out to when compiling a program to native code. Keep the major in
  # sync with the inkwell feature (llvm22-1) the compiler is built against.
  depends_on "llvm@22"
  depends_on :macos

  def install
    bin.install "prism"
  end

  test do
    (testpath/"hello.pr").write <<~PRISM
      fn main() : !{IO} Unit =
        println(42)
    PRISM
    assert_match "42", shell_output("#{bin}/prism run #{testpath}/hello.pr")
  end
end
