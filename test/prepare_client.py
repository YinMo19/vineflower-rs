"""Prepare the Minecraft 26.3 input layouts used for CLI memory comparisons."""

import argparse
from contextlib import ExitStack
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile, ZipInfo


SUBTREES = {
    760: (
        "com/mojang/blaze3d/", "net/minecraft/advancements/", "net/minecraft/nbt/",
        "net/minecraft/network/chat/", "net/minecraft/server/commands/",
    ),
    2831: (
        "com/mojang/renderpearl/", "net/minecraft/client/gui/", "net/minecraft/network/",
        "net/minecraft/server/", "net/minecraft/world/item/",
    ),
}


def write_entry(archive, name, data):
    # Fixed timestamp, Unix permissions and stored contents make identical JARs
    # across machines while preserving the client's central-directory order.
    entry = ZipInfo(name)
    entry.create_system = 3
    entry.external_attr = (0o40755 << 16 | 0x10) if entry.is_dir() else 0o100644 << 16
    archive.writestr(entry, data)


def prepare(source, destination, prefixes):
    destination.parent.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(dir=destination.parent) as temporary:
        output = Path(temporary) / "inputs"
        output.mkdir()
        with ZipFile(source) as client, ExitStack() as files:
            combined = files.enter_context(ZipFile(output / "combined.jar", "w"))
            external = files.enter_context(ZipFile(output / "external.jar", "w"))
            parts = {
                prefix: files.enter_context(ZipFile(output / f"part-{i}.jar", "w"))
                for i, prefix in enumerate(prefixes, 1)
            }
            for entry in client.infolist():
                name = entry.filename
                if name == "META-INF/LICENSE":
                    part = parts[prefixes[0]]
                elif entry.is_dir() or name.endswith(".class"):
                    part = next(
                        (jar for prefix, jar in parts.items() if name.startswith(prefix)),
                        None,
                    )
                else:
                    continue
                if part is not None:
                    data = client.read(entry)
                    write_entry(part, name, data)
                    write_entry(combined, name, data)
                elif name.endswith(".class"):
                    write_entry(external, name, client.read(entry))
        output.rename(destination)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("client", type=Path)
    parser.add_argument("classes", type=int, choices=SUBTREES)
    parser.add_argument("destination", type=Path, help="new directory for the generated JARs")
    args = parser.parse_args()
    prepare(args.client, args.destination, SUBTREES[args.classes])
