# Security Policy

This security policy applies to the "core" crates in the rust-bitcoin ecosystem, which are
`bitcoin`, `secp256k1`, `bitcoin_hashes` and `bitcoin-private`. These crates deal with
cryptography and cryptographic algorithms, and as such, are likely locations for security
vulnerabilities to crop up.

As a general rule, an issue is a security vulnerability if it could lead to:

* Loss of funds
* Loss of privacy
* Censorship (including e.g. by attaching an incorrectly low fee to a transaction)
* Any "ordinary" security problem, such as remote code execution or invalid memory acccess

In general, use your best judgement in determining whether an issue is a security issue. If not,
go ahead and post it to the public issue tracker.

**If you believe you are aware of a security issue**, please contact Andrew Poelstra at
`rust-bitcoin-security@wpsoftware.net`. You may GPG-encrypt this email to his public key, which
[can be downloaded from his website here](https://wpsoftware.net/andrew/andrew.gpg) or which is
listed in full below.

# Andrew Poelstra's GPG Key

-----BEGIN PGP PUBLIC KEY BLOCK-----

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
FLOK24IUW7uqkzZWsEyU37lVEWZw8i6ov/VbYphTsSwGZvrX5EhPhalQK306esJY
ucTQ+cuQ165QxZRISk1M/teoyhGJP5f+A3Ec0ctF0PO8fbBx1A7TiQF7BBIBCABl
BQJS+Yo3XhSAAAAAABUAQGJsb2NraGFzaEBiaXRjb2luLm9yZzAwMDAwMDAwMDAw
MDAwMDBjODRhMDRhNzAyMzI1Y2YzY2RmNGEzNDQzNjJlZDBjMTllYzgxN2E5MDE0
ZWVlYzcACgkQf6sRQmfk+gTeWAf+I/v9anL0GzK/MQ1v80qysizrbbfrab8vojLK
n/vVqoX7B85uVE+B/Mp9FDAQ0mMnD1Yn1PsWwX3fr4du4Jr+jRXRqupF5GLU5LlW
NfP1VwY/49zUpUx2ka+aGgOCNhsr0VZrqZPt8qjDSVlvX1twrc7P1bWk0Y/e4Y4z
whBDNZ3luge2fakVuxdk1eoLwrgHARCt2MnFkcNm4pZiNyeTnWlDgcKDFatRkXSE
czC3jTC6cLBaOjR1p7lzXthAAlUPbOUcztNCOhjhoEQu05pQQB8yN9lChCachsc/
oKGEWkFgl4UsuYtBx8iJB8lYw3Yvl2gEOTA0oIyXzKnRLt6iiokCHAQQAQIABgUC
VA9iQAAKCRBQfh+DfBT/qeW9EACWx2O20PEGQA3QpJfXR4ocJD4iXfYNYwu9Du26
2RKwLLDpVxCgXDUIlH2EfVaQNQF/jatz78UnukPAbCmQz7n85lvlU64R1P1Mv1/W
80f+211mb+K3V6mAE4vQtJTMis7vW+c4lv30QNwkQ9n4YFz9fqfRm3qacy1ydAdM
wnigV/L+M10IRnYMB6A2Z2lYLmvvCtKWkBSXvl9r8LVJRsVT2DSzw4O762YcuVXN
quLV1aGp5pe/8w0DKd+OYJrEyYi1Qj+Svod2J6OEobDTISqBdi0KGujelaDaCDwB
teTZBdjBgWh+YG+cRBoq6jNPF4tiyU34kcVHsZflyNyCgUmJsSSgJW7D4KqXZoEy
WpsIALAf9xCAh16Uj5zyci3Dyk61Gj9C9ykhdEHfONGVhNF9G8lmGc9SGz8lNoJd
SMQ63TsWqxo62D1Ap+BIzr6EImets16gbRs5J4w1bV1g5Vb22SlpuFScE6wRO+S3
W+onsr3xfj2Q1faUxmFjkcjAgBPMz2Q2RuV3+m3FusI8RgcpyNpCLr6cJD2JaKTR
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
phpfVPK3mthha1GaE5j3cYyuFGNViBAaEkPpBS0JOmt66+LIjx+tZ0t4rVHG/oIP
GdD9QMvToWzxGqTI1zjQtcJpud84q0zTokdzKhfZMdc3fC8SJWKhrpUYHlC311Jj
if5IU2TDfPWIQ1Oesz/OcfAxjf/WXBijYj0obbXNkYHqtXKmBg4NQn4yVF0OBpUk
3MdbWAVsUH6mNiVTA16tLPekSr522u+pCo24zQF9RhNOvtrxRuyVjduzzYjFK+kG
47UgZBqjg8gOZdFh2tdjeuevE4yuxAmzcNYhCYLE7czMz+7br3qozHKR7/PGfcqg
WHy8x72OCoutpA1PMtHVydXHARAAAQEAAAAAAAAAAAAAAAD/2P/gABBKRklGAAEB
AQBIAEgAAP/+ADtDUkVBVE9SOiBnZC1qcGVnIHYxLjAgKHVzaW5nIElKRyBKUEVH
IHY2MiksIHF1YWxpdHkgPSA5MAr/2wBDABcQERQRDhcUEhQaGBcbIjklIh8fIkYy
NSk5UkhXVVFIUE5bZoNvW2F8Yk5QcptzfIeLkpSSWG2grJ+OqoOPko3/2wBDARga
GiIeIkMlJUONXlBejY2NjY2NjY2NjY2NjY2NjY2NjY2NjY2NjY2NjY2NjY2NjY2N
jY2NjY2NjY2NjY2NjY3/wgARCAEYARgDAREAAhEBAxEB/8QAGQABAQEBAQEAAAAA
AAAAAAAAAAECAwQF/8QAFwEBAQEBAAAAAAAAAAAAAAAAAAECA//aAAwDAQACEAMQ
AAAB92NAAAAACFBBUiigAACFEKIlBGgAAACFAIQyQ80uztZDoWkKAEKCACLFoSLQ
gKQGI5r41zAzbzTRQdz23PSgJACghSBqBBVliKARzXzZvmt50M2CWalhDR1j6Vzo
tABCgECwAUECkeaXzzXIxoOdhFZSqKQ6S+mTsemyigAQoFzQQoIBlfJm+deenOwE
ErKaC0RpbHoPoXNoQpBCkDUoICkgMS/OmuOksynWahiyWalENEBo3H0LnrQQoIAV
rNAAiAcpfnNYoUKklZs0qFAEyU9UnvuVoAQoI1KBCkBmPLLxWLo2QhDNQVUQqHCw
dY+lc6oCgAGs0ACA4xwzeN13jsaMmQZrFQAEThXG52v02elICwJQNywFBAco8udc
rfbHUVkzEJWahAkBivLYPoM96SBbQBG5QECCuceGai++NCsmYzUIQlQIIeWs2eyT
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
dpxrlOWOxI9jmzuQ75LO
=WxeH
-----END PGP PUBLIC KEY BLOCK-----
