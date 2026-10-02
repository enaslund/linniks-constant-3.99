"""Read per-root gzip JSON files or their byte-preserving indexed ZIP archive.

Loose files take precedence, allowing isolated test fixtures and later repairs.
Each process opens its own cached ZIP handle; readers never write either form.
"""
from functools import lru_cache
import gzip
import json
import os
from pathlib import Path
import re
from zipfile import ZipFile


def name(idx):
    assert type(idx) is int and idx>=0
    return f'{idx:04d}.json.gz'


def _id(filename):
    match=re.fullmatch(r'([0-9]{4,})\.json\.gz',filename)
    if match is None:return None
    idx=int(match[1])
    assert filename==name(idx), 'Noncanonical root filename'
    return idx


@lru_cache(maxsize=8)
def _opened(path,pid,size,mtime_ns):
    archive=ZipFile(path)
    names=archive.namelist()
    assert len(names)==len(set(names)), 'Duplicate archive member'
    assert all(_id(member) is not None for member in names), 'Unexpected archive member'
    return archive


def _archive(directory):
    path=Path(directory)/'roots.zip'
    if not path.exists():return None
    stat=path.stat()
    return _opened(str(path.resolve()),os.getpid(),stat.st_size,stat.st_mtime_ns)


def root_ids(directory):
    directory=Path(directory)
    ids={idx for path in directory.glob('*.json.gz') if (idx:=_id(path.name)) is not None}
    archive=_archive(directory)
    if archive is not None:ids.update(_id(member) for member in archive.namelist())
    return sorted(ids)


def has_root(directory,idx):
    filename=name(idx)
    if (Path(directory)/filename).is_file():return True
    archive=_archive(directory)
    return archive is not None and filename in archive.NameToInfo


def read_root_bytes(directory,idx):
    filename=name(idx);path=Path(directory)/filename
    if path.is_file():return path.read_bytes()
    archive=_archive(directory)
    if archive is None or filename not in archive.NameToInfo:raise FileNotFoundError(path)
    return archive.read(filename)


def read_root(directory,idx):
    result=json.loads(gzip.decompress(read_root_bytes(directory,idx)))
    assert result['id']==idx, 'Root ID differs from its filename'
    return result
