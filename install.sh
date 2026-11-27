#!/bin/sh
set -eu

die() {
    printf 'Error: %s\n' "$*" >&2
    exit 1
}

install_vineflower() {
    if [ -z "${PATH:-}" ]; then
        PATH=/usr/bin:/bin
        export PATH
    fi

    system=$(uname -s)
    machine=$(uname -m)
    case "$system" in
        Darwin)
            platform=apple-darwin
            # A shell running under Rosetta reports x86_64 on Apple Silicon.
            if [ "$machine" = x86_64 ] &&
                [ "$(PATH="$PATH:/usr/sbin" sysctl -n sysctl.proc_translated 2>/dev/null)" = 1 ]; then
                machine=arm64
            fi
            ;;
        Linux)  platform=unknown-linux-gnu ;;
        *) die "Unsupported operating system: $system" ;;
    esac
    case "$machine" in
        x86_64)        arch=x86_64 ;;
        arm64|aarch64) arch=aarch64 ;;
        *) die "Unsupported architecture: $machine" ;;
    esac
    asset="vineflower-rs-$arch-$platform"
    release_url=https://github.com/YinMo19/vineflower-rs/releases/latest/download

    if [ -n "${VINEFLOWER_INSTALL_DIR:-}" ]; then
        install_dir=$VINEFLOWER_INSTALL_DIR
    else
        [ -n "${HOME:-}" ] || die 'Set HOME or VINEFLOWER_INSTALL_DIR before installing.'
        install_dir=$HOME/.local/bin
    fi
    case "$install_dir" in
        /*) ;;
        *) install_dir=$PWD/$install_dir ;;
    esac
    command -v curl >/dev/null 2>&1 || die 'curl is required.'
    if command -v sha256sum >/dev/null 2>&1; then
        hash_tool=sha256sum
    elif command -v shasum >/dev/null 2>&1; then
        hash_tool=shasum
    else
        die 'Install sha256sum or shasum to verify the download.'
    fi

    mkdir -p "$install_dir"
    destination=$install_dir/vineflower-rs
    [ ! -d "$destination" ] || die "Destination is a directory: $destination"
    # Stage on the same filesystem so the verified binary can replace an existing install atomically.
    staging=$(mktemp -d "$install_dir/.vineflower-rs.XXXXXXXX")
    trap 'rm -rf "$staging"' 0
    trap 'exit 1' HUP INT TERM

    printf 'Downloading %s\n' "$asset"
    for file in "$asset" SHA256SUMS; do
        curl -fsSL --proto '=https' --proto-redir '=https' \
            -o "$staging/$file" "$release_url/$file" || die "Download failed: $file"
    done
    expected=$(awk -v asset="$asset" '
        NF == 2 && ($2 == asset || $2 == "*" asset) { print $1; count++ }
        END { if (count != 1) exit 1 }
    ' "$staging/SHA256SUMS") || die "Expected one SHA256SUMS entry for $asset."
    if [ "$hash_tool" = sha256sum ]; then
        digest=$(sha256sum < "$staging/$asset")
    else
        digest=$(shasum -a 256 < "$staging/$asset")
    fi
    [ "${digest%% *}" = "$expected" ] || die "SHA-256 mismatch for $asset."

    chmod 755 "$staging/$asset"
    mv -f "$staging/$asset" "$destination"
    printf 'Installed %s\n' "$destination"
    case ":${PATH:-}:" in
        *:"$install_dir":*) ;;
        *)
            quoted_dir=$(printf '%s\n' "$install_dir" | sed "s/'/'\\\\''/g")
            printf '%s\n' 'Add this directory to PATH in your shell:' \
                "  export PATH='$quoted_dir'\${PATH:+:\$PATH}"
            ;;
    esac
    printf '%s\n' 'Run vineflower-rs --help to get started.'
}

install_vineflower
