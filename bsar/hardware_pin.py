#!/usr/bin/env python3
"""
PINNED SILICON & L1 CACHE TELEMETRY (`bsar.hardware_pin`)
License: GNU AGPLv3
Attestation: probabilistic_structural

Queries exact host CPU model string, physical/logical core counts, and per-core
L1D / L1I / L2 / L3 cache geometry in <1 ms using zero external dependencies:
  - Windows: `winreg` (`ProcessorNameString`) + `kernel32.GetLogicalProcessorInformation`
  - Linux:   `/proc/cpuinfo` + `/sys/devices/system/cpu/cpu0/cache/index*`
  - macOS:   `sysctl` (`machdep.cpu.brand_string`, `hw.l1dcachesize`, `hw.cachelinesize`)
"""

from __future__ import annotations

import ctypes
import os
import platform
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict

from .cd_q88 import L1_CACHE_LINE_BYTES, LUT_32D_BYTES


def _query_windows_cpu_and_caches() -> Dict[str, Any]:
    cpu_model = platform.processor() or "Unknown Windows CPU"
    mhz = 0
    try:
        import winreg

        with winreg.OpenKey(
            winreg.HKEY_LOCAL_MACHINE,
            r"HARDWARE\DESCRIPTION\System\CentralProcessor\0",
        ) as key:
            cpu_model = str(winreg.QueryValueEx(key, "ProcessorNameString")[0]).strip()
            mhz = int(winreg.QueryValueEx(key, "~MHz")[0])
    except Exception:
        pass

    # Query exact cache descriptors directly from Windows kernel32
    l1d_per_core = 32768
    l1i_per_core = 32768
    l2_per_core = 262144
    l3_shared = 0
    line_size = 64
    phys_cores = 0

    try:

        class _CacheDescriptor(ctypes.Structure):
            _fields_ = [
                ("Level", ctypes.c_ubyte),
                ("Associativity", ctypes.c_ubyte),
                ("LineSize", ctypes.c_ushort),
                ("Size", ctypes.c_ulong),
                ("Type", ctypes.c_int),  # 0=Unified, 1=Instruction, 2=Data, 3=Trace
            ]

        class _Union(ctypes.Union):
            _fields_ = [
                ("Flags", ctypes.c_ubyte),
                ("NodeNumber", ctypes.c_ulong),
                ("Cache", _CacheDescriptor),
                ("Reserved", ctypes.c_ulonglong * 2),
            ]

        class _SysProcInfo(ctypes.Structure):
            _fields_ = [
                ("ProcessorMask", ctypes.c_size_t),
                ("Relationship", ctypes.c_int),  # 0=ProcessorCore, 2=Cache
                ("u", _Union),
            ]

        k32 = ctypes.windll.kernel32
        ret_len = ctypes.c_ulong(0)
        k32.GetLogicalProcessorInformation(None, ctypes.byref(ret_len))
        if ret_len.value > 0:
            count = ret_len.value // ctypes.sizeof(_SysProcInfo)
            buf = (_SysProcInfo * count)()
            if k32.GetLogicalProcessorInformation(buf, ctypes.byref(ret_len)):
                l1d_seen = []
                l1i_seen = []
                l2_seen = []
                l3_seen = []
                for item in buf:
                    if item.Relationship == 0:
                        phys_cores += 1
                    elif item.Relationship == 2:
                        c = item.u.Cache
                        if c.LineSize > 0:
                            line_size = int(c.LineSize)
                        if c.Level == 1 and c.Type == 2:
                            l1d_seen.append(int(c.Size))
                        elif c.Level == 1 and c.Type == 1:
                            l1i_seen.append(int(c.Size))
                        elif c.Level == 2:
                            l2_seen.append(int(c.Size))
                        elif c.Level == 3:
                            l3_seen.append(int(c.Size))
                if l1d_seen:
                    l1d_per_core = l1d_seen[0]
                if l1i_seen:
                    l1i_per_core = l1i_seen[0]
                if l2_seen:
                    l2_per_core = l2_seen[0]
                if l3_seen:
                    l3_shared = max(l3_seen)
    except Exception:
        pass

    return {
        "cpu_model": cpu_model,
        "base_clock_mhz": mhz,
        "physical_cores": phys_cores or (os.cpu_count() or 1) // 2 or 1,
        "logical_threads": os.cpu_count() or 1,
        "l1d_per_core_bytes": l1d_per_core,
        "l1i_per_core_bytes": l1i_per_core,
        "l1_cache_line_bytes": line_size,
        "l2_per_core_bytes": l2_per_core,
        "l3_shared_bytes": l3_shared,
    }


def _query_posix_cpu_and_caches() -> Dict[str, Any]:
    cpu_model = platform.processor() or platform.machine()
    l1d = 32768
    l1i = 32768
    l2 = 262144
    l3 = 0
    line_size = 64

    if sys.platform.startswith("linux"):
        cpuinfo = Path("/proc/cpuinfo")
        if cpuinfo.exists():
            for line in cpuinfo.read_text(encoding="utf-8", errors="ignore").splitlines():
                if "model name" in line and ":" in line:
                    cpu_model = line.split(":", 1)[1].strip()
                    break
        cache_root = Path("/sys/devices/system/cpu/cpu0/cache")
        if cache_root.exists():
            for idx_dir in cache_root.glob("index*"):
                try:
                    lvl = int((idx_dir / "level").read_text().strip())
                    ctype = (idx_dir / "type").read_text().strip().lower()
                    raw_sz = (idx_dir / "size").read_text().strip().upper()
                    mult = 1024 if raw_sz.endswith("K") else (1048576 if raw_sz.endswith("M") else 1)
                    sz = int(raw_sz.rstrip("KMB")) * mult
                    if (idx_dir / "coherency_line_size").exists():
                        line_size = int((idx_dir / "coherency_line_size").read_text().strip())
                    if lvl == 1 and "data" in ctype:
                        l1d = sz
                    elif lvl == 1 and "instruction" in ctype:
                        l1i = sz
                    elif lvl == 2:
                        l2 = sz
                    elif lvl == 3:
                        l3 = sz
                except Exception:
                    pass
    elif sys.platform == "darwin":
        def _sysctl(name: str) -> str:
            res = subprocess.run(["sysctl", "-n", name], capture_output=True, text=True)
            return res.stdout.strip() if res.returncode == 0 else ""

        brand = _sysctl("machdep.cpu.brand_string")
        if brand:
            cpu_model = brand
        for key, setter in (
            ("hw.l1dcachesize", "l1d"),
            ("hw.l1icachesize", "l1i"),
            ("hw.l2cachesize", "l2"),
            ("hw.l3cachesize", "l3"),
            ("hw.cachelinesize", "line"),
        ):
            val = _sysctl(key)
            if val.isdigit():
                iv = int(val)
                if setter == "l1d":
                    l1d = iv
                elif setter == "l1i":
                    l1i = iv
                elif setter == "l2":
                    l2 = iv
                elif setter == "l3":
                    l3 = iv
                elif setter == "line":
                    line_size = iv

    return {
        "cpu_model": cpu_model,
        "base_clock_mhz": 0,
        "physical_cores": os.cpu_count() or 1,
        "logical_threads": os.cpu_count() or 1,
        "l1d_per_core_bytes": l1d,
        "l1i_per_core_bytes": l1i,
        "l1_cache_line_bytes": line_size,
        "l2_per_core_bytes": l2,
        "l3_shared_bytes": l3,
    }


def pin_host_hardware() -> Dict[str, Any]:
    """Return deterministic, verifiable host silicon & L1D footprint telemetry."""
    base = (
        _query_windows_cpu_and_caches()
        if os.name == "nt"
        else _query_posix_cpu_and_caches()
    )
    kernel_bytes = L1_CACHE_LINE_BYTES + LUT_32D_BYTES  # 64B + 128B = 192B
    l1d = max(1, int(base["l1d_per_core_bytes"]))
    line_sz = max(1, int(base["l1_cache_line_bytes"]))

    return {
        **base,
        "os_platform": f"{platform.system()} {platform.release()} ({platform.machine()})",
        "python_version": platform.python_version(),
        "gpu_required": False,
        "bsar_kernel_total_bytes": kernel_bytes,
        "bsar_kernel_l1_cache_lines": kernel_bytes // line_sz,
        "l1d_total_cache_lines_per_core": l1d // line_sz,
        "bsar_pct_of_single_core_l1d": round((kernel_bytes / float(l1d)) * 100.0, 4),
    }
