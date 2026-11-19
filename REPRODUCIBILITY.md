# Checking equation (10.19) from the public sources

The target is `NavierStokesR3.Paper1019.equation_10_19`. The public package supplies 14 Lean source modules and their checksums. A build also needs Lean 4.34.0-rc2, the upstream Navier–Stokes sources and 11 locked Lake dependencies. Fetching these inputs requires network access. The frozen logs, compiled objects, verification scripts and dependency mirrors remain private. Independent reproduction and mathematical review are pending.

## Inputs

| Input | Pinned revision |
|---|---|
| [Lean 4.34.0-rc2](https://github.com/leanprover/lean4/releases/tag/v4.34.0-rc2), including Lake and leanchecker | `6a10ac8c22beadecabdbb0919c2b50214762f91d` |
| [OpenAI upstream sources](https://github.com/openai/NavierStokesAndEuler/tree/f9e8bc5b38b6e212696e8a30e3e91517af887bbd) | `f9e8bc5b38b6e212696e8a30e3e91517af887bbd` |
| [Mathlib](https://github.com/leanprover-community/mathlib4/tree/85e3a25e006c35636f0e53b0e9296caca2685bc0) | `85e3a25e006c35636f0e53b0e9296caca2685bc0` |

The upstream checkout contains `lean-toolchain`, `lakefile.toml` and [the lockfile for all 11 packages](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/lake-manifest.json). Use Git, Python 3.9 or later, and the pinned Lean release with `lean` and `lake` available on the command line.

## Build and inspect

Start in the extracted directory containing `SHA256SUMS` and `lean/`. Save the following Python block as `rebuild_local.py` in your own working copy and run `python rebuild_local.py` there. It checks the listed files, creates a fresh sibling directory named `ns1019-review`, fetches the locked sources, and builds the companion modules and their imports. A source build of Mathlib's required modules may take substantial time and disk space.

```python
import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path


def run(*args, cwd):
    subprocess.run(args, cwd=cwd, check=True)


def revision(folder):
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=folder, text=True
    ).strip()


def checkout(folder, url, rev):
    folder.mkdir(parents=True)
    run("git", "init", "-q", cwd=folder)
    run("git", "config", "core.autocrlf", "false", cwd=folder)
    run("git", "config", "core.longpaths", "true", cwd=folder)
    run("git", "remote", "add", "origin", url, cwd=folder)
    run("git", "fetch", "--depth=1", "origin", rev, cwd=folder)
    run("git", "checkout", "--detach", rev, cwd=folder)
    if revision(folder) != rev:
        raise ValueError(f"Revision mismatch in {folder.name}")


public = Path.cwd()
for line in (public / "SHA256SUMS").read_text(encoding="utf8").splitlines():
    digest, name = line.split("  ", 1)
    if hashlib.sha256((public / name).read_bytes()).hexdigest() != digest:
        raise ValueError(f"Checksum mismatch in {name}")

repo = public.parent / "ns1019-review"
checkout(repo, "https://github.com/openai/NavierStokesAndEuler.git",
         "f9e8bc5b38b6e212696e8a30e3e91517af887bbd")
version = subprocess.check_output(["lean", "--version"], cwd=repo, text=True)
if "6a10ac8c22beadecabdbb0919c2b50214762f91d" not in version:
    raise ValueError("Unexpected Lean compiler")
print(version.strip(), flush=True)

lock = (repo / "lake-manifest.json").read_bytes()
if hashlib.sha256(lock).hexdigest() != "5ec1dc8e009008d0efb9601cd38f6ba54e753fd538b0e5f8c3e6c5ec72ee1e09":
    raise ValueError("Unexpected dependency lockfile")
packages = json.loads(lock)["packages"]
package_dir = repo / ".lake" / "packages"
for package in packages:
    checkout(package_dir / package["name"], package["url"], package["rev"])

modules = sorted((public / "lean").glob("*.lean"))
if len(modules) != 14:
    raise ValueError("Expected 14 companion modules")
with (repo / "lakefile.toml").open("a", encoding="utf8") as lakefile:
    for module in modules:
        target = repo / module.name
        if target.exists():
            raise FileExistsError(target.name)
        shutil.copyfile(module, target)
        lakefile.write(f'\n[[lean_lib]]\nname = "{module.stem}"\n')
        lakefile.write('leanOptions = { warningAsError = true }\n')

os.environ["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
run("lake", "--no-cache", "build", *[f"+{p.stem}:olean" for p in modules], cwd=repo)
for package in packages:
    if revision(package_dir / package["name"]) != package["rev"]:
        raise ValueError(f"Dependency revision changed for {package['name']}")

name = "NavierStokesR3.Paper1019.equation_10_19"
check = repo / "Check1019.lean"
check.write_text(f"import Paper1019\n#check {name}\n#print axioms {name}\n", encoding="utf8")
run("lake", "env", "lean", check.name, cwd=repo)
for module in modules:
    run("lake", "env", "leanchecker", "-v", module.stem, cwd=repo)
```

The companion import graph uses 58 modules from the pinned OpenAI repository. Lake also resolves their external dependencies. A successful run prints the theorem's type in a fresh Lean process and completes all 14 kernel checks. The expected axiom report for this theorem lists `propext`, `Classical.choice` and `Quot.sound`. The public recipe was checked against the pinned inputs and import graph during packaging. A new end-to-end build was not part of that check.

For mathematical review, compare the type with Lemma 10.5 and equation (10.19) on printed page 123. In particular, compare the physical flux, the cutoff powers, the energy premise and the order of the constant, radius and time quantifiers. [Original manuscript](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf#page=123)
