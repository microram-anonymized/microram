#!/usr/bin/env python3
"""Run TLS tests with temporary, locally generated credentials (no network)."""

from pathlib import Path
import subprocess
import sys
import tempfile


def invoke(arguments, timeout=30):
    result = subprocess.run(list(map(str, arguments)), text=True, capture_output=True,
                            timeout=timeout)
    if result.returncode:
        raise RuntimeError(f"command failed: {arguments[0]}\n{result.stdout}{result.stderr}")
    return result.stdout


def credentials(directory, openssl):
    def command(*args):
        return invoke([openssl, *args])

    for name in ("ca", "wrong-ca"):
        command("req", "-x509", "-newkey", "rsa:2048", "-nodes", "-sha256",
                "-days", "2", "-subj", f"/CN=MPT test {name}",
                "-addext", "basicConstraints=critical,CA:TRUE",
                "-addext", "keyUsage=critical,keyCertSign,cRLSign",
                "-keyout", directory / f"{name}-key.pem",
                "-out", directory / f"{name}.pem")
    for serial, (name, ca, purpose) in enumerate(
            (("server", "ca", "serverAuth"), ("client", "ca", "clientAuth"),
             ("rogue-client", "wrong-ca", "clientAuth")), 1):
        command("req", "-new", "-newkey", "rsa:2048", "-nodes", "-sha256",
                "-subj", f"/CN=MPT test {name}",
                "-keyout", directory / f"{name}-key.pem",
                "-out", directory / f"{name}.csr")
        extensions = ("basicConstraints=critical,CA:FALSE\n"
                      "keyUsage=critical,digitalSignature,keyEncipherment\n"
                      f"extendedKeyUsage={purpose}\n")
        if name == "server":
            extensions += "subjectAltName=DNS:localhost\n"
        extfile = directory / f"{name}.ext"
        extfile.write_text(extensions, encoding="ascii")
        command("x509", "-req", "-sha256", "-days", "2", "-set_serial", serial,
                "-in", directory / f"{name}.csr", "-CA", directory / f"{ca}.pem",
                "-CAkey", directory / f"{ca}-key.pem", "-extfile", extfile,
                "-out", directory / f"{name}.pem")


def main(arguments):
    demo_only = bool(arguments and arguments[0] == "--demo-only")
    if demo_only:
        arguments = arguments[1:]
    expected = 2 if demo_only else 3
    if len(arguments) != expected:
        raise SystemExit("usage: transport_test.py TEST_BINARY DEMO_BINARY OPENSSL_BINARY\n"
                         "   or: transport_test.py --demo-only DEMO_BINARY OPENSSL_BINARY")
    demo, openssl = arguments[-2:]
    with tempfile.TemporaryDirectory(prefix="mpt tls tests ") as temporary:
        directory = Path(temporary)
        credentials(directory, openssl)
        if not demo_only:
            print(invoke([arguments[0], directory], timeout=120), end="")
        output = invoke([demo, "--ca", directory / "ca.pem",
                         "--server-cert", directory / "server.pem",
                         "--server-key", directory / "server-key.pem",
                         "--client-cert", directory / "client.pem",
                         "--client-key", directory / "client-key.pem",
                         "--server-name", "localhost"], timeout=120)
        print(output, end="")


if __name__ == "__main__":
    main(sys.argv[1:])
