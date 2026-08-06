#!/usr/bin/env python3
"""Build native packages and refresh release packaging metadata."""

from __future__ import annotations

import argparse
import os
import platform
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Sequence


ROOT = Path(__file__).resolve().parent.parent


def run(command: Sequence[str], *, env: dict[str, str] | None = None) -> int:
    return subprocess.run(command, cwd=ROOT, env=env, check=False).returncode


def native(version: str) -> int:
    if platform.system() == "Darwin":
        print(
            "WARN: packaging a macOS binary; the deb/rpm will not run on Linux",
            file=sys.stderr,
        )
    machine = platform.machine().lower()
    architectures = {
        "x86_64": "amd64",
        "amd64": "amd64",
        "aarch64": "arm64",
        "arm64": "arm64",
    }
    if machine not in architectures:
        print(f"unsupported architecture: {machine}", file=sys.stderr)
        return 1

    env = os.environ.copy()
    env.update(VERSION=version, PKG_ARCH=architectures[machine])
    destination = ROOT / "dist"
    destination.mkdir(exist_ok=True)
    # The binary is linked against glibc, so Alpine users get the container
    # rather than a misleading apk package.
    for package_format in ("deb", "rpm", "archlinux"):
        status = run(
            [
                "nfpm",
                "package",
                "-f",
                "packaging/nfpm.yaml",
                "-p",
                package_format,
                "-t",
                "dist",
            ],
            env=env,
        )
        if status:
            return status
    for path in sorted(destination.iterdir()):
        print(path.name)
    return 0


def pkgbuild(version: str) -> int:
    with tempfile.TemporaryDirectory(prefix="prism-pkgbuild-") as directory:
        status = run(
            [
                "gh",
                "release",
                "download",
                f"v{version}",
                "-D",
                directory,
                "--clobber",
                "-p",
                f"prism-{version}-x86_64-unknown-linux-gnu.tar.gz.sha256",
                "-p",
                f"prism-{version}-aarch64-unknown-linux-gnu.tar.gz.sha256",
            ]
        )
        if status:
            return status
        return run(
            [
                "scripts/gen-pkgbuild.sh",
                version,
                directory,
                "packaging/arch/PKGBUILD",
            ]
        )


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    subcommands = command.add_subparsers(dest="task", required=True)
    for name, help_text in (
        ("native", "build host-native packages"),
        ("pkgbuild", "refresh packaging/arch/PKGBUILD"),
    ):
        task = subcommands.add_parser(name, help=help_text)
        task.add_argument("version")
    return command


def main() -> int:
    arguments = parser().parse_args()
    if arguments.task == "native":
        return native(arguments.version)
    if arguments.task == "pkgbuild":
        return pkgbuild(arguments.version)
    raise AssertionError(f"unhandled task: {arguments.task}")


if __name__ == "__main__":
    sys.exit(main())
