"""
Remove files that a pure-Python wheel does not need at run time (e.g. the generated C sources of `dd`'s
optional Cython extensions, about 1 MB) and drop them from the wheel's RECORD.

    python3 slim_wheel.py WHEEL PATTERN...     # PATTERN is an fnmatch pattern of archive member names
"""
import fnmatch
import os
import sys
import tempfile
import zipfile


def slim(wheel_path: str, patterns: list) -> int:
    def is_removed(name: str) -> bool:
        return any(fnmatch.fnmatch(name, pattern) for pattern in patterns)

    removed = 0
    fd, tmp_path = tempfile.mkstemp(suffix='.whl', dir=os.path.dirname(os.path.abspath(wheel_path)))
    os.close(fd)
    with zipfile.ZipFile(wheel_path) as source, zipfile.ZipFile(tmp_path, 'w', zipfile.ZIP_DEFLATED) as target:
        for info in source.infolist():
            if is_removed(info.filename):
                removed += 1
                continue
            data = source.read(info)
            if info.filename.endswith('.dist-info/RECORD'):
                lines = data.decode().splitlines()
                data = ''.join(f'{line}\n' for line in lines if not is_removed(line.split(',', 1)[0])).encode()
            target.writestr(info, data)
    os.chmod(tmp_path, os.stat(wheel_path).st_mode & 0o777)  # mkstemp creates the file with mode 0600
    os.replace(tmp_path, wheel_path)
    return removed


if __name__ == '__main__':
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    print(f'{sys.argv[1]}: removed {slim(sys.argv[1], sys.argv[2:])} files')
