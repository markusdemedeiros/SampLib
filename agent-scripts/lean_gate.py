#!/usr/bin/env python3
"""Limit concurrent proof checks to fit the shared machine's memory."""

from __future__ import annotations

import fcntl
from pathlib import Path
import subprocess
import sys
import tempfile
import time


def main() -> int:
    command = sys.argv[1:]
    if command[:1] == ["--"]:
        command = command[1:]
    if not command:
        raise SystemExit("usage: lean_gate.py -- COMMAND [ARG ...]")
    directory = Path(tempfile.gettempdir()) / "samplib-lean-slots"
    directory.mkdir(exist_ok=True)
    slots = [(directory / str(i)).open("a") for i in range(4)]
    admission = (directory / "admission").open("a")
    acquired = None
    try:
        # Serialize admission so new jobs cannot race every existing waiter for
        # each freed slot. Running jobs retain the same three memory locks.
        fcntl.flock(admission, fcntl.LOCK_EX)
        while acquired is None:
            for slot in slots:
                try:
                    fcntl.flock(slot, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    continue
                acquired = slot
                break
            if acquired is None:
                time.sleep(0.25)
        fcntl.flock(admission, fcntl.LOCK_UN)
        child = subprocess.Popen(command)
        try:
            return child.wait()
        finally:
            if child.poll() is None:
                child.terminate()
                child.wait()
    finally:
        admission.close()
        for slot in slots:
            slot.close()


if __name__ == "__main__":
    raise SystemExit(main())
