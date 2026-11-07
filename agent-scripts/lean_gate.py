#!/usr/bin/env python3
"""Limit concurrent proof checks to fit the shared machine's memory."""

from __future__ import annotations

import fcntl
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time


SLOTS = 3
# Lake compiles one module per Lean worker thread; cap each job so the slots, not the
# core count, bound memory.
THREADS_PER_JOB = "2"


def main() -> int:
    command = sys.argv[1:]
    if command[:1] == ["--"]:
        command = command[1:]
    if not command:
        raise SystemExit("usage: lean_gate.py -- COMMAND [ARG ...]")
    directory = Path(tempfile.gettempdir()) / "samplib-lean-slots"
    directory.mkdir(exist_ok=True)
    slots = [(directory / str(i)).open("a") for i in range(SLOTS)]
    admission = (directory / "admission").open("a")
    acquired = None
    try:
        # Serialize admission so new jobs cannot race every existing waiter for
        # each freed slot.
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
        env = dict(os.environ)
        env.setdefault("LEAN_NUM_THREADS", THREADS_PER_JOB)
        child = subprocess.Popen(command, env=env)
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
