/**
 * Asymmetric (ed25519) Standard Webhooks signing and verification.
 *
 * The spec's current asymmetric scheme is `v2a`, provided by
 * $(LREF AsymmetricVerifier) and $(LREF AsymmetricSigner): it signs a SHA-256
 * digest of `{endpointId}.{id}.{timestamp}.{payload}`, so one key pair can serve
 * every endpoint and the key can live in a KMS or HSM.
 *
 * $(LREF AsymmetricWebhook) implements the earlier `v1a` scheme, which the spec
 * now deprecates: the same
 * `{id}.{timestamp}.{payload}` content as the symmetric `v1` scheme, signed with
 * an ed25519 private key and verified with the matching public key. Unlike the
 * symmetric scheme, the verifier holds only a public key, so a leaked verifier
 * cannot forge messages.
 *
 * Keys use the Standard Webhooks serialisation: a `whsk_`-prefixed base64
 * signing key (64 bytes, `seed ‖ public_key`) and a `whpk_`-prefixed base64
 * public key (32 bytes). Construct an $(LREF AsymmetricWebhook) from either —
 * from a `whsk_` key it can both sign and verify; from a `whpk_` key it can only
 * verify.
 *
 * This subpackage links the system libsodium for the ed25519 primitives, so it
 * is kept out of the dependency-free core. Depend on `standardwebhooks:ed25519`
 * and `import standardwebhooks.ed25519;`.
 *
 * Example:
 * ---
 * // Receiver holds only the public key.
 * auto verifier = AsymmetricWebhook("whpk_1SiA4o9hyqTCpIqC5V9HUakiiaeACeqfZTInDBbOir4=");
 * verifier.verify(payload, headers);
 *
 * // Sender holds the signing key.
 * auto signer = AsymmetricWebhook("whsk_...");
 * auto headers = signer.signHeaders("msg_2b3c", 1614265330, `{"event":"ping"}`);
 * ---
 */
module standardwebhooks.ed25519;

import std.base64 : Base64;
import std.conv : to;
import std.datetime.systime : SysTime;

import standardwebhooks;
import standardwebhooks.internal;
import standardwebhooks.sodium;

@safe:

/// The signature version tag the asymmetric scheme produces and accepts.
private enum string asymmetricVersion = "v1a";

/// The prefix that brands a base64 ed25519 public (verify-only) key.
private enum string publicKeyPrefix = "whpk_";
/// The prefix that brands a base64 ed25519 signing key.
private enum string signingKeyPrefix = "whsk_";

/**
 * Signs and verifies Standard Webhooks payloads with an ed25519 key pair.
 *
 * Constructed from a `whpk_` public key (verify only) or a `whsk_` signing key
 * (sign and verify), or generated deterministically from a 32-byte seed via
 * $(LREF fromSeed). The type is a lightweight value: copying it shares the
 * immutable key bytes.
 */
struct AsymmetricWebhook
{
	private immutable(ubyte)[] publicKey;
	/// The 64-byte libsodium secret key (`seed ‖ public_key`), or empty when the
	/// instance was built from a public key alone.
	private immutable(ubyte)[] secretKey;

	/// The timestamp tolerance window in unix seconds; defaults to
	/// $(REF defaultToleranceSeconds, standardwebhooks,webhook) (five minutes).
	/// The window is symmetric: a message verifies when its timestamp lies
	/// within `±toleranceSeconds` of the current time, guarding against both
	/// stale (replayed) and future-dated payloads. A value `<= 0` rejects
	/// nearly every message, while a very large value effectively disables
	/// replay protection by accepting arbitrarily old timestamps.
	long toleranceSeconds = defaultToleranceSeconds;

	/**
	 * Builds an `AsymmetricWebhook` from a serialised key.
	 *
	 * A `whsk_` key yields an instance that can both sign and verify; a `whpk_`
	 * key yields a verify-only instance.
	 *
	 * Throws: $(REF WebhookException, standardwebhooks,exception)
	 *   with `emptySecret` for an empty string, or `invalidSecret` if the prefix
	 *   is unrecognised, the base64 is malformed, or the decoded key is the wrong
	 *   length.
	 */
	this(string key)
	{
		if (key.length == 0)
			throw new WebhookException("Key can't be empty.", WebhookError.emptySecret);

		if (hasPrefix(key, signingKeyPrefix))
		{
			auto bytes = decodePrefixedKey(key, signingKeyPrefix);
			if (bytes.length != secretKeyBytes)
				throw new WebhookException("Invalid ed25519 signing key length",
						WebhookError.invalidSecret);
			this.secretKey = bytes;
			this.publicKey = bytes[seedBytes .. $];
		}
		else if (hasPrefix(key, publicKeyPrefix))
		{
			auto bytes = decodePrefixedKey(key, publicKeyPrefix);
			if (bytes.length != publicKeyBytes)
				throw new WebhookException("Invalid ed25519 public key length",
						WebhookError.invalidSecret);
			this.publicKey = bytes;
		}
		else
			throw new WebhookException("Asymmetric key must be prefixed with whsk_ or whpk_",
					WebhookError.invalidSecret);
	}

	/**
	 * Derives a sign-and-verify `AsymmetricWebhook` from a 32-byte ed25519 seed.
	 * The seed should come from a cryptographically secure source.
	 *
	 * This is the asymmetric scheme's key-generation entry point; the symmetric
	 * $(REF Webhook, standardwebhooks,webhook) has no equivalent and is instead
	 * constructed directly from an existing secret string or raw key bytes via
	 * its `fromRaw`.
	 *
	 * Throws: $(REF WebhookException, standardwebhooks,exception)
	 *   with `invalidSecret` if `seed` is not exactly 32 bytes.
	 */
	static AsymmetricWebhook fromSeed(scope const(ubyte)[] seed)
	{
		if (seed.length != seedBytes)
			throw new WebhookException("ed25519 seed must be 32 bytes", WebhookError.invalidSecret);

		ubyte[publicKeyBytes] pk;
		ubyte[secretKeyBytes] sk;
		if (()@trusted {
				ensureSodiumInitialised();
				return crypto_sign_seed_keypair(pk.ptr, sk.ptr, seed.ptr);
			}() != 0)
			throw new WebhookException("ed25519 key derivation failed", WebhookError.cryptoFailure);

		AsymmetricWebhook wh;
		wh.publicKey = pk.idup;
		// The persisted secret key lives in immutable GC memory and is not wiped:
		// copies alias the same backing array, so zeroing it would be unsound. Only
		// the transient stack buffer below is wiped once its bytes are copied out.
		wh.secretKey = sk.idup;
		() @trusted { sodium_memzero(sk.ptr, sk.length); }();
		return wh;
	}

	/**
	 * Builds a verify-only `AsymmetricWebhook` from a raw 32-byte ed25519 public
	 * key, sparing the caller the base64-encode-then-decode round trip of the
	 * `whpk_` string constructor.
	 *
	 * Throws: $(REF WebhookException, standardwebhooks,exception)
	 *   with `invalidSecret` if `pk` is not exactly 32 bytes.
	 */
	static AsymmetricWebhook fromRawPublicKey(scope const(ubyte)[] pk)
	{
		if (pk.length != publicKeyBytes)
			throw new WebhookException("ed25519 public key must be 32 bytes",
					WebhookError.invalidSecret);

		AsymmetricWebhook wh;
		wh.publicKey = pk.idup;
		return wh;
	}

	/**
	 * Builds a sign-and-verify `AsymmetricWebhook` from a raw 64-byte ed25519
	 * secret key in the libsodium `seed ‖ public_key` layout, sparing the caller
	 * the base64-encode-then-decode round trip of the `whsk_` string constructor.
	 *
	 * Throws: $(REF WebhookException, standardwebhooks,exception)
	 *   with `invalidSecret` if `sk` is not exactly 64 bytes.
	 */
	static AsymmetricWebhook fromRawSecretKey(scope const(ubyte)[] sk)
	{
		if (sk.length != secretKeyBytes)
			throw new WebhookException("ed25519 secret key must be 64 bytes",
					WebhookError.invalidSecret);

		AsymmetricWebhook wh;
		wh.secretKey = sk.idup;
		wh.publicKey = wh.secretKey[seedBytes .. $];
		return wh;
	}

	/**
	 * Returns a copy of this `AsymmetricWebhook` with its timestamp tolerance set
	 * to `seconds`, sharing the same key bytes. Tolerance is key-independent, so
	 * the copy preserves every invariant; this enables fluent construction such
	 * as `AsymmetricWebhook(key).withTolerance(600).verify(...)`.
	 */
	AsymmetricWebhook withTolerance(long seconds) const
	{
		AsymmetricWebhook wh;
		wh.publicKey = this.publicKey;
		wh.secretKey = this.secretKey;
		wh.toleranceSeconds = seconds;
		return wh;
	}

	/// Whether this instance holds a signing key and so can $(LREF sign).
	bool canSign() const
	{
		return secretKey.length != 0;
	}

	/// The public key in `whpk_`-prefixed base64 form — the value a sender shares
	/// with receivers so they can verify.
	string publicKeyEncoded() const
	{
		return publicKeyPrefix ~ Base64.encode(publicKey).idup;
	}

	/**
	 * The signing key in `whsk_`-prefixed base64 form.
	 *
	 * Throws: $(REF WebhookException, standardwebhooks,exception)
	 *   with `signingKeyRequired` if this is a verify-only instance.
	 */
	string signingKeyEncoded() const
	{
		requireSigningKey();
		return signingKeyPrefix ~ Base64.encode(secretKey).idup;
	}

	/**
	 * Signs `payload` and returns a single versioned signature of the form
	 * `v1a,<base64>` — the value to place in (or append to) the
	 * `webhook-signature` header.
	 *
	 * Throws: $(REF WebhookException, standardwebhooks,exception)
	 *   with `signingKeyRequired` if this is a verify-only instance, or with
	 *   `cryptoFailure` if libsodium fails to initialise.
	 */
	string sign(string msgId, long timestamp, scope const(char)[] payload) const
	{
		requireSigningKey();
		const content = buildSignedContent(msgId, timestamp.to!string, payload);
		return asymmetricVersion ~ "," ~ signDetached(secretKey, content);
	}

	/// Convenience overload taking a `SysTime`; truncates to unix seconds.
	string sign(string msgId, SysTime timestamp, scope const(char)[] payload) const
	{
		return sign(msgId, timestamp.toUnixTime(), payload);
	}

	/**
	 * Signs `payload` and returns the three Standard Webhooks headers ready to
	 * attach to an outgoing HTTP request.
	 */
	string[string] signHeaders(string msgId, long timestamp, scope const(char)[] payload) const
	{
		return [
			headerId: msgId,
			headerTimestamp: timestamp.to!string,
			headerSignature: sign(msgId, timestamp, payload),
		];
	}

	/**
	 * Verifies that `payload` carries a valid `v1a` signature for the given
	 * headers and that its timestamp is within tolerance of now.
	 *
	 * Header keys are matched case-insensitively, with the Svix-branded `svix-*`
	 * aliases accepted as a fallback, exactly as in the symmetric scheme.
	 *
	 * Returns: `payload` unchanged, for convenient chaining.
	 *
	 * Throws: $(REF WebhookException, standardwebhooks,exception)
	 *   if a required header is missing, the timestamp is unparseable or outside
	 *   tolerance, no signature matches, or libsodium fails to initialise.
	 *
	 * A blanket `catch -> 400` is wrong here: a `cryptoFailure` cause is a
	 * server/library fault and should map to a 5xx, not a 400. Branch on
	 * `WebhookException.error` to distinguish it from the bad-request
	 * causes.
	 */
	const(char)[] verify(scope return const(char)[] payload, in string[string] headers) const
	{
		return throwOnFailure(tryVerify(payload, headers));
	}

	/**
	 * Like $(LREF verify) but skips the timestamp tolerance check entirely. Use
	 * only when replay protection is handled elsewhere.
	 *
	 * Throws: $(REF WebhookException, standardwebhooks,exception)
	 *   if a required header is missing, no signature matches, or libsodium fails
	 *   to initialise.
	 */
	const(char)[] verifyIgnoringTimestamp(scope return const(char)[] payload,
			in string[string] headers) const
	{
		return throwOnFailure(tryVerifyIgnoringTimestamp(payload, headers));
	}

	/**
	 * Verifies `payload` against `headers` without throwing, returning a
	 * $(REF VerifyResult, standardwebhooks,exception). An invalid inbound
	 * signature is routine control flow for a receiver, so callers branch on the
	 * result's `error` instead of catching. The throwing $(LREF verify) is built
	 * on this, so the two stay in lock-step.
	 *
	 * Header matching and the timestamp window behave exactly as in $(LREF verify).
	 */
	VerifyResult tryVerify(scope return const(char)[] payload, in string[string] headers) const
	{
		return tryVerifyAt(payload, headers, currentUnixSeconds(), true);
	}

	/**
	 * Like $(LREF tryVerify) but skips the timestamp tolerance check entirely. Use
	 * only when replay protection is handled elsewhere.
	 */
	VerifyResult tryVerifyIgnoringTimestamp(scope return const(char)[] payload,
			in string[string] headers) const
	{
		return tryVerifyAt(payload, headers, currentUnixSeconds(), false);
	}

	/// Verifies against an explicit `now` (unix seconds). Exposed for
	/// deterministic testing of the tolerance window.
	package const(char)[] verifyAt(scope return const(char)[] payload,
			in string[string] headers, long now, bool checkTimestamp) const
	{
		return throwOnFailure(tryVerifyAt(payload, headers, now, checkTimestamp));
	}

	/// The non-throwing verification core, against an explicit `now`. Exposed for
	/// deterministic testing of the tolerance window.
	package VerifyResult tryVerifyAt(scope return const(char)[] payload,
			in string[string] headers, long now, bool checkTimestamp) const
	{
		const(char)[] msgId, tsHeader, sigHeader;
		WebhookError error;
		if (!tryRequireHeaders(headers, now, checkTimestamp, toleranceSeconds,
				msgId, tsHeader, sigHeader, error))
			return VerifyResult(false, error);

		const content = buildSignedContent(msgId, tsHeader, payload);

		const matched = anySignature(sigHeader, (scope version_, scope signature) {
			return version_ == asymmetricVersion && verifyDetached(publicKey, content, signature);
		});
		if (matched)
			return VerifyResult(true, WebhookError.init, payload);

		return VerifyResult(false, WebhookError.noMatch);
	}

	private void requireSigningKey() const
	{
		if (secretKey.length == 0)
			throw new WebhookException("A whsk_ signing key is required to sign",
					WebhookError.signingKeyRequired);
	}
}

// --- v2a: endpoint-bound signatures over a SHA-256 digest -------------------

/// The signature version tag of the current asymmetric scheme.
private enum string asymmetricV2Version = "v2a";

/// DER prefix of an ed25519 SubjectPublicKeyInfo, followed by the raw 32-byte
/// public key (the form AWS KMS `GetPublicKey` returns, for example).
private immutable ubyte[12] ed25519SpkiPrefix = [
	0x30, 0x2a, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x03, 0x21, 0x00
];

/**
 * Verifies webhooks signed with the spec's asymmetric `v2a` scheme.
 *
 * `v2a` signs `SHA-256("{endpointId}.{id}.{timestamp}.{payload}")` with pure
 * ed25519. Because the endpoint ID is part of the signed content, one key pair
 * can serve every endpoint (the spec recommends one per environment) and can
 * live in a KMS or HSM, without a webhook for one endpoint being replayable to
 * another. The producer shares the endpoint ID with the consumer alongside the
 * public key; it is never sent with the webhook.
 *
 * Constructed with the endpoint ID and the list of trusted `whpk_` public keys,
 * newest first. A webhook verifies if any `v2a` entry in its
 * `webhook-signature` header was made by any trusted key, so a producer rotates
 * keys by having consumers add the new key to the front of the list. Other
 * signature versions (`v1`, the deprecated `v1a`) are skipped.
 *
 * Example:
 * ---
 * auto verifier = AsymmetricVerifier("ep_2fVZdC8Kx9TR4ZoCqHWt3NnLgRb",
 *     "whpk_uWKK13PfwqyOgrqT0OrWKcS2uVD7e89+oUKnkoPjx7w=");
 * verifier.verify(payload, headers);
 * ---
 */
struct AsymmetricVerifier
{
	private string endpointId_;
	private immutable(ubyte)[][] publicKeys;

	/// The timestamp tolerance window in unix seconds, as for
	/// $(LREF AsymmetricWebhook.toleranceSeconds).
	long toleranceSeconds = defaultToleranceSeconds;

	/**
	 * Builds a verifier for the endpoint `endpointId` trusting `publicKeys`, each
	 * a `whpk_`-prefixed base64 ed25519 public key, ordered newest first.
	 *
	 * Throws: $(REF WebhookException, standardwebhooks,exception) with
	 *   `invalidEndpointId` if `endpointId` is empty or contains a `.`,
	 *   `emptySecret` if no key is given, or `invalidSecret` if a key lacks the
	 *   `whpk_` prefix, is not valid base64 or is not 32 bytes.
	 */
	this(string endpointId, scope const(string)[] publicKeys...)
	{
		requireValidEndpointId(endpointId);
		if (publicKeys.length == 0)
			throw new WebhookException("At least one public key is required",
					WebhookError.emptySecret);

		foreach (key; publicKeys)
		{
			if (!hasPrefix(key, publicKeyPrefix))
				throw new WebhookException("Public key must be prefixed with whpk_",
						WebhookError.invalidSecret);
			auto bytes = decodePrefixedKey(key, publicKeyPrefix);
			if (bytes.length != publicKeyBytes)
				throw new WebhookException("Invalid ed25519 public key length",
						WebhookError.invalidSecret);
			this.publicKeys ~= bytes;
		}
		this.endpointId_ = endpointId;
	}

	/// Builds a verifier from raw 32-byte ed25519 public keys, newest first.
	///
	/// Throws: as the string constructor, with `invalidSecret` for a key that is
	///   not exactly 32 bytes.
	static AsymmetricVerifier fromRawPublicKeys(string endpointId,
			scope const(ubyte[])[] publicKeys...)
	{
		requireValidEndpointId(endpointId);
		if (publicKeys.length == 0)
			throw new WebhookException("At least one public key is required",
					WebhookError.emptySecret);

		AsymmetricVerifier v;
		foreach (pk; publicKeys)
		{
			if (pk.length != publicKeyBytes)
				throw new WebhookException("ed25519 public key must be 32 bytes",
						WebhookError.invalidSecret);
			v.publicKeys ~= pk.idup;
		}
		v.endpointId_ = endpointId;
		return v;
	}

	/// The endpoint ID this verifier checks signatures for.
	string endpointId() const
	{
		return endpointId_;
	}

	/// Returns a copy with its timestamp tolerance set to `seconds`, sharing the
	/// same keys.
	AsymmetricVerifier withTolerance(long seconds) const
	{
		AsymmetricVerifier v;
		v.endpointId_ = endpointId_;
		v.publicKeys = cast(immutable(ubyte)[][]) publicKeys.dup;
		v.toleranceSeconds = seconds;
		return v;
	}

	/**
	 * Verifies that `payload` carries a valid `v2a` signature for the given
	 * headers and that its timestamp is within tolerance of now. Header matching
	 * is as in $(LREF AsymmetricWebhook.verify).
	 *
	 * Returns: `payload` unchanged, for convenient chaining.
	 *
	 * Throws: $(REF WebhookException, standardwebhooks,exception) if a required
	 *   header is missing, the timestamp is unparseable or outside tolerance, no
	 *   signature matches, or libsodium fails to initialise (`cryptoFailure`,
	 *   which should map to a 5xx rather than a 400).
	 */
	const(char)[] verify(scope return const(char)[] payload, in string[string] headers) const
	{
		return throwOnFailure(tryVerify(payload, headers));
	}

	/// Like $(LREF verify) but skips the timestamp tolerance check. Use only when
	/// replay protection is handled elsewhere.
	const(char)[] verifyIgnoringTimestamp(scope return const(char)[] payload,
			in string[string] headers) const
	{
		return throwOnFailure(tryVerifyIgnoringTimestamp(payload, headers));
	}

	/// Non-throwing $(LREF verify), returning a
	/// $(REF VerifyResult, standardwebhooks,exception).
	VerifyResult tryVerify(scope return const(char)[] payload, in string[string] headers) const
	{
		return tryVerifyAt(payload, headers, currentUnixSeconds(), true);
	}

	/// Non-throwing $(LREF verifyIgnoringTimestamp).
	VerifyResult tryVerifyIgnoringTimestamp(scope return const(char)[] payload,
			in string[string] headers) const
	{
		return tryVerifyAt(payload, headers, currentUnixSeconds(), false);
	}

	/// The non-throwing verification core, against an explicit `now`. Exposed for
	/// deterministic testing of the tolerance window.
	package VerifyResult tryVerifyAt(scope return const(char)[] payload,
			in string[string] headers, long now, bool checkTimestamp) const
	{
		const(char)[] msgId, tsHeader, sigHeader;
		WebhookError error;
		if (!tryRequireHeaders(headers, now, checkTimestamp, toleranceSeconds,
				msgId, tsHeader, sigHeader, error))
			return VerifyResult(false, error);

		if (publicKeys.length == 0)
			return VerifyResult(false, WebhookError.emptySecret);

		try
			ensureSodiumInitialised();
		catch (WebhookException e)
			return VerifyResult(false, e.error);

		// The timestamp header is used verbatim, as in the other schemes, so a
		// sender's exact formatting round-trips.
		const digest = v2aDigest(endpointId_, msgId, tsHeader, payload);

		const matched = anySignature(sigHeader, (scope version_, scope signature) {
			if (version_ != asymmetricV2Version)
				return false;
			foreach (pk; publicKeys)
				if (verifyDetachedBytes(pk, digest[], signature))
					return true;
			return false;
		});
		if (matched)
			return VerifyResult(true, WebhookError.init, payload);

		return VerifyResult(false, WebhookError.noMatch);
	}

	/**
	 * Calculates the response to an endpoint verification challenge, per the
	 * Standard Webhooks endpoint verification (WEV) extension, using the first
	 * (newest) public key. Takes the `webhook-challenge` header exactly as
	 * received and returns the `webhook-challenge-response` value
	 * (`v2a,<base64>`). See
	 * $(REF Webhook.endpointVerificationResponse, standardwebhooks,webhook).
	 *
	 * Throws: $(REF WebhookException, standardwebhooks,exception) with
	 *   `emptySecret` for an `AsymmetricVerifier.init` that has no key.
	 */
	string endpointVerificationResponse(scope const(char)[] challenge) const
	{
		if (publicKeys.length == 0)
			throw new WebhookException("At least one public key is required",
					WebhookError.emptySecret);
		return challengeResponse(publicKeys[0], challenge);
	}

	/**
	 * Producer side of endpoint verification: whether `response` is the correct
	 * answer to `challenge` for any of the trusted keys. The whole value,
	 * including the `v2a,` identifier, is compared in constant time.
	 */
	bool isValidEndpointVerificationResponse(scope const(char)[] challenge,
			scope const(char)[] response) const
	{
		bool matched;
		foreach (pk; publicKeys)
			matched |= constantTimeEquals(response, challengeResponse(pk, challenge));
		return matched;
	}

	/// Like $(LREF isValidEndpointVerificationResponse) but throws a
	/// $(REF WebhookException, standardwebhooks,exception) with `noMatch` on
	/// mismatch.
	void verifyEndpointVerificationResponse(scope const(char)[] challenge,
			scope const(char)[] response) const
	{
		if (!isValidEndpointVerificationResponse(challenge, response))
			throw new WebhookException("No matching signature found", WebhookError.noMatch);
	}

	private string challengeResponse(scope const(ubyte)[] pk, scope const(char)[] challenge) const
	{
		// endpoint_key = public key bytes ‖ "." ‖ endpoint ID
		const endpointKey = pk ~ cast(const(ubyte)[]) "." ~ cast(const(ubyte)[]) endpointId_;
		return asymmetricV2Version ~ "," ~ endpointVerificationSignature(endpointKey, challenge);
	}
}

/**
 * Signs webhooks with the spec's asymmetric `v2a` scheme, using an ed25519
 * private key held by the producer.
 *
 * A signer is not tied to an endpoint: one key pair serves all of them, and the
 * endpoint ID is passed per signature. Producers holding the key in a KMS or
 * HSM sign $(LREF asymmetricSignedContentHash) there instead and format the
 * result with $(LREF formatAsymmetricSignature).
 *
 * Example:
 * ---
 * auto signer = AsymmetricSigner("whsk_4uKPjji/dhB8w6GW3YYDnIMYvXcdHrvH6lidTr4Z+EY=");
 * auto headers = signer.signHeaders("ep_2fVZdC8Kx9TR4ZoCqHWt3NnLgRb",
 *     "msg_2KWPBgLlAfxdpx2AI54pPJ85f4W", 1674087231, payload);
 * string share = signer.publicKeyEncoded(); // give to consumers with the endpoint ID
 * ---
 */
struct AsymmetricSigner
{
	private immutable(ubyte)[] secretKey; // libsodium seed ‖ public key, 64 bytes

	/**
	 * Builds a signer from a `whsk_` key. The spec serialises the 32-byte ed25519
	 * seed; the 64-byte `seed ‖ public_key` form used by
	 * $(LREF AsymmetricWebhook) is also accepted, so an existing `v1a` key pair
	 * can move to `v2a` unchanged.
	 *
	 * Throws: $(REF WebhookException, standardwebhooks,exception) with
	 *   `emptySecret` for an empty string, `invalidSecret` if the prefix is
	 *   missing, the base64 is malformed, the length is wrong or a 64-byte key's
	 *   public half does not match its seed, or `cryptoFailure` if libsodium
	 *   fails.
	 */
	this(string key)
	{
		if (key.length == 0)
			throw new WebhookException("Key can't be empty.", WebhookError.emptySecret);
		if (!hasPrefix(key, signingKeyPrefix))
			throw new WebhookException("Signing key must be prefixed with whsk_",
					WebhookError.invalidSecret);

		auto bytes = decodePrefixedKey(key, signingKeyPrefix);
		if (bytes.length == seedBytes)
			this = fromSeed(bytes);
		else if (bytes.length == secretKeyBytes)
		{
			auto derived = fromSeed(bytes[0 .. seedBytes]);
			if (derived.secretKey[seedBytes .. $] != bytes[seedBytes .. $])
				throw new WebhookException(
						"ed25519 signing key's public half does not match its seed",
						WebhookError.invalidSecret);
			this = derived;
		}
		else
			throw new WebhookException("Invalid ed25519 signing key length",
					WebhookError.invalidSecret);
	}

	/**
	 * Builds a signer from a raw 32-byte ed25519 seed, which should come from a
	 * cryptographically secure source.
	 *
	 * Throws: $(REF WebhookException, standardwebhooks,exception) with
	 *   `invalidSecret` if `seed` is not 32 bytes, or `cryptoFailure`.
	 */
	static AsymmetricSigner fromSeed(scope const(ubyte)[] seed)
	{
		if (seed.length != seedBytes)
			throw new WebhookException("ed25519 seed must be 32 bytes", WebhookError.invalidSecret);

		ubyte[publicKeyBytes] pk;
		ubyte[secretKeyBytes] sk;
		if (()@trusted {
				ensureSodiumInitialised();
				return crypto_sign_seed_keypair(pk.ptr, sk.ptr, seed.ptr);
			}() != 0)
			throw new WebhookException("ed25519 key derivation failed", WebhookError.cryptoFailure);

		AsymmetricSigner signer;
		// As in AsymmetricWebhook.fromSeed, only the transient buffer is wiped.
		signer.secretKey = sk.idup;
		() @trusted { sodium_memzero(sk.ptr, sk.length); }();
		return signer;
	}

	/// The public key in `whpk_` form: share it with consumers together with
	/// each endpoint's ID.
	string publicKeyEncoded() const
	{
		requireKey();
		return publicKeyPrefix ~ Base64.encode(secretKey[seedBytes .. $]).idup;
	}

	/// The signing key in the spec's `whsk_` form (the base64 32-byte seed).
	string signingKeyEncoded() const
	{
		requireKey();
		return signingKeyPrefix ~ Base64.encode(secretKey[0 .. seedBytes]).idup;
	}

	/**
	 * Signs `payload` for the endpoint `endpointId` and returns a single
	 * `v2a,<base64>` entry for the `webhook-signature` header.
	 *
	 * Throws: $(REF WebhookException, standardwebhooks,exception) with
	 *   `invalidEndpointId` for an empty endpoint ID or one containing `.`,
	 *   `signingKeyRequired` for an `AsymmetricSigner.init`, or `cryptoFailure`.
	 */
	string sign(string endpointId, string msgId, long timestamp, scope const(char)[] payload) const
	{
		requireKey();
		const digest = asymmetricSignedContentHash(endpointId, msgId, timestamp, payload);
		return asymmetricV2Version ~ "," ~ signDetachedBytes(secretKey, digest[]);
	}

	/// Convenience overload taking a `SysTime`; truncates to unix seconds.
	string sign(string endpointId, string msgId, SysTime timestamp, scope const(char)[] payload) const
	{
		return sign(endpointId, msgId, timestamp.toUnixTime(), payload);
	}

	/// Signs `payload` for `endpointId` and returns the three Standard Webhooks
	/// headers for the outgoing request.
	string[string] signHeaders(string endpointId, string msgId, long timestamp,
			scope const(char)[] payload) const
	{
		return [
			headerId: msgId,
			headerTimestamp: timestamp.to!string,
			headerSignature: sign(endpointId, msgId, timestamp, payload),
		];
	}

	private void requireKey() const
	{
		if (secretKey.length == 0)
			throw new WebhookException("A whsk_ signing key is required to sign",
					WebhookError.signingKeyRequired);
	}
}

/**
 * The SHA-256 digest of the content a `v2a` signature covers,
 * `{endpointId}.{msgId}.{timestamp}.{payload}`, as raw bytes.
 *
 * For producers that sign in a KMS or HSM: sign these 32 bytes with pure
 * ed25519 and pass the signature to $(LREF formatAsymmetricSignature).
 *
 * Throws: $(REF WebhookException, standardwebhooks,exception) with
 *   `invalidEndpointId` if `endpointId` is empty or contains a `.`.
 */
ubyte[32] asymmetricSignedContentHash(string endpointId, string msgId,
		long timestamp, scope const(char)[] payload)
{
	requireValidEndpointId(endpointId);
	return v2aDigest(endpointId, msgId, timestamp.to!string, payload);
}

/**
 * Formats a raw 64-byte ed25519 signature as a `v2a,<base64>` entry for the
 * `webhook-signature` header.
 *
 * Throws: $(REF WebhookException, standardwebhooks,exception) with
 *   `invalidSecret` if `signature` is not 64 bytes.
 */
string formatAsymmetricSignature(scope const(ubyte)[] signature)
{
	if (signature.length != signatureBytes)
		throw new WebhookException("ed25519 signature must be 64 bytes", WebhookError.invalidSecret);
	return asymmetricV2Version ~ "," ~ Base64.encode(signature).idup;
}

/**
 * Formats an ed25519 public key as `whpk_<base64>` to share with consumers.
 * Accepts the raw 32-byte key or its DER-encoded SubjectPublicKeyInfo (what a
 * KMS such as AWS KMS `GetPublicKey` returns).
 *
 * Throws: $(REF WebhookException, standardwebhooks,exception) with
 *   `invalidSecret` for any other input.
 */
string formatAsymmetricPublicKey(scope const(ubyte)[] publicKey)
{
	if (publicKey.length == ed25519SpkiPrefix.length + publicKeyBytes)
	{
		if (publicKey[0 .. ed25519SpkiPrefix.length] != ed25519SpkiPrefix[])
			throw new WebhookException("Not an ed25519 SubjectPublicKeyInfo",
					WebhookError.invalidSecret);
		publicKey = publicKey[ed25519SpkiPrefix.length .. $];
	}
	if (publicKey.length != publicKeyBytes)
		throw new WebhookException("ed25519 public key must be 32 bytes",
				WebhookError.invalidSecret);
	return publicKeyPrefix ~ Base64.encode(publicKey).idup;
}

/// Rejects an endpoint ID the spec does not allow: empty, or containing `.`
/// (which would make the signed content ambiguous).
private void requireValidEndpointId(scope const(char)[] endpointId)
{
	import std.string : indexOf;

	if (endpointId.length == 0 || endpointId.indexOf('.') >= 0)
		throw new WebhookException("Endpoint ID may not be empty or contain '.'",
				WebhookError.invalidEndpointId);
}

/// SHA-256 of `{endpointId}.{msgId}.{tsStr}.{payload}`, hashed incrementally so
/// a large payload is not copied.
private ubyte[32] v2aDigest(scope const(char)[] endpointId,
		scope const(char)[] msgId, scope const(char)[] tsStr, scope const(char)[] payload)
{
	import std.digest.sha : SHA256;

	SHA256 h;
	h.start();
	h.put(cast(const(ubyte)[]) endpointId);
	h.put('.');
	h.put(cast(const(ubyte)[]) msgId);
	h.put('.');
	h.put(cast(const(ubyte)[]) tsStr);
	h.put('.');
	h.put(cast(const(ubyte)[]) payload);
	return h.finish();
}

// --- Dual-scheme verification -----------------------------------------------

/**
 * Verifies `payload` against either scheme: a symmetric `v1` $(REF Webhook,
 * standardwebhooks,webhook) or an asymmetric `v1a` $(LREF AsymmetricWebhook).
 *
 * A receiver that accepts both schemes builds one verifier of each and passes
 * them here. Each is tried in turn — symmetric first, then asymmetric — and the
 * payload is returned as soon as one accepts it. If neither does, the
 * asymmetric verifier's exception is propagated.
 *
 * Both verifiers apply their own `toleranceSeconds`; verification runs against
 * the current clock.
 *
 * Returns: `payload` unchanged, for convenient chaining.
 *
 * Throws: $(REF WebhookException, standardwebhooks,exception)
 *   if neither scheme accepts the payload.
 */
const(char)[] verifyAny(in Webhook symmetric, in AsymmetricWebhook asymmetric,
		scope return const(char)[] payload, in string[string] headers)
{
	return verifyAnyAt(symmetric, asymmetric, payload, headers, currentUnixSeconds(), true);
}

/**
 * Like $(LREF verifyAny) but skips the timestamp tolerance check on both
 * verifiers. Use only when replay protection is handled elsewhere.
 *
 * Throws: $(REF WebhookException, standardwebhooks,exception)
 *   if neither scheme accepts the payload.
 */
const(char)[] verifyAnyIgnoringTimestamp(in Webhook symmetric,
		in AsymmetricWebhook asymmetric, scope return const(char)[] payload,
		in string[string] headers)
{
	return verifyAnyAt(symmetric, asymmetric, payload, headers, currentUnixSeconds(), false);
}

/// Tries both schemes against an explicit `now` (unix seconds). Exposed for
/// deterministic testing of the dual-scheme path.
package const(char)[] verifyAnyAt(in Webhook symmetric, in AsymmetricWebhook asymmetric,
		scope return const(char)[] payload, in string[string] headers, long now, bool checkTimestamp)
{
	try
		return symmetric.verifyAt(payload, headers, now, checkTimestamp);
	catch (WebhookException e)
	{
		// A symmetric operator/config fault (an empty secret, or a tolerance
		// window that admits nothing) is the receiver's own misconfiguration,
		// not a rejected payload. Surface it instead of silently degrading to
		// asymmetric-only verification.
		if (e.error == WebhookError.emptySecret || e.error == WebhookError.invalidTolerance)
			throw e;
		// The symmetric scheme rejected the payload; fall through to the
		// asymmetric scheme, whose exception is surfaced if it too rejects.
		return asymmetric.verifyAt(payload, headers, now, checkTimestamp);
	}
}

/**
 * Verifies `payload` against either scheme without throwing, returning a
 * $(REF VerifyResult, standardwebhooks,exception). This is the non-throwing
 * counterpart to $(LREF verifyAny): an invalid inbound signature is routine
 * control flow for a receiver, so callers branch on the result's `error`
 * instead of catching.
 *
 * Each scheme is tried in turn — symmetric first, then asymmetric — and the
 * first acceptance wins. If neither accepts the payload, the asymmetric
 * verifier's result is returned, naming its cause.
 *
 * Both verifiers apply their own `toleranceSeconds`; verification runs against
 * the current clock.
 */
VerifyResult tryVerifyAny(in Webhook symmetric, in AsymmetricWebhook asymmetric,
		scope return const(char)[] payload, in string[string] headers)
{
	return tryVerifyAnyAt(symmetric, asymmetric, payload, headers, currentUnixSeconds(), true);
}

/**
 * Like $(LREF tryVerifyAny) but skips the timestamp tolerance check on both
 * verifiers. Use only when replay protection is handled elsewhere.
 */
VerifyResult tryVerifyAnyIgnoringTimestamp(in Webhook symmetric,
		in AsymmetricWebhook asymmetric, scope return const(char)[] payload,
		in string[string] headers)
{
	return tryVerifyAnyAt(symmetric, asymmetric, payload, headers, currentUnixSeconds(), false);
}

/// The non-throwing dual-scheme core, against an explicit `now` (unix seconds).
/// Exposed for deterministic testing of the dual-scheme path.
package VerifyResult tryVerifyAnyAt(in Webhook symmetric, in AsymmetricWebhook asymmetric,
		scope return const(char)[] payload, in string[string] headers, long now, bool checkTimestamp)
{
	auto symmetricResult = symmetric.tryVerifyAt(payload, headers, now, checkTimestamp);
	if (symmetricResult.ok)
		return symmetricResult;

	// The symmetric scheme rejected the payload; fall through to the asymmetric
	// scheme, whose result is surfaced whether or not it too rejects.
	return asymmetric.tryVerifyAt(payload, headers, now, checkTimestamp);
}

// --- Free helpers -----------------------------------------------------------

/// Whether `s` begins with `prefix`.
private bool hasPrefix(scope const(char)[] s, string prefix) @safe
{
	return s.length >= prefix.length && s[0 .. prefix.length] == prefix;
}

/// Produces the base64 ed25519 signature (without the `v1a,` prefix) of
/// `content` under the 64-byte secret key `sk`.
private string signDetached(scope const(ubyte)[] sk, scope const(char)[] content) @trusted
{
	ensureSodiumInitialised();
	ubyte[signatureBytes] sig;
	ulong siglen;
	if (crypto_sign_detached(sig.ptr, &siglen,
			cast(const(ubyte)*) content.ptr, content.length, sk.ptr) != 0)
		throw new WebhookException("ed25519 signing failed", WebhookError.cryptoFailure);
	if (siglen != signatureBytes)
		throw new WebhookException("ed25519 signing produced unexpected length",
				WebhookError.cryptoFailure);
	return Base64.encode(sig[0 .. siglen]).idup;
}

/// Produces the base64 ed25519 signature of the raw bytes `message` under the
/// 64-byte secret key `sk`.
private string signDetachedBytes(scope const(ubyte)[] sk, scope const(ubyte)[] message) @trusted
{
	return signDetached(sk, cast(const(char)[]) message);
}

/// Verifies a base64 ed25519 `signature` over the raw bytes `message`.
private bool verifyDetachedBytes(scope const(ubyte)[] pk,
		scope const(ubyte)[] message, scope const(char)[] signature) @trusted
{
	return verifyDetached(pk, cast(const(char)[]) message, signature);
}

/// Verifies a base64 ed25519 `signature` over `content` against public key `pk`.
/// A malformed or wrong-length signature returns false rather than throwing.
private bool verifyDetached(scope const(ubyte)[] pk, scope const(char)[] content,
		scope const(char)[] signature) @trusted
{
	ensureSodiumInitialised();

	// The spec mandates canonical standard padded base64 for v1a signatures, as
	// the symmetric v1 scheme requires. Reject an unpadded length here so the
	// padding-tolerant core decode cannot silently accept a non-canonical value.
	if (signature.length % 4 != 0)
		return false;

	immutable(ubyte)[] decoded;
	try
		decoded = decodeStdBase64(signature);
	catch (Exception)
		return false;

	if (decoded.length != signatureBytes)
		return false;

	return crypto_sign_verify_detached(decoded.ptr,
			cast(const(ubyte)*) content.ptr, content.length, pk.ptr) == 0;
}

// --- Tests ------------------------------------------------------------------
// Golden vector from the Svix server's `test_asymmetric_key_signing`, the
// de-facto reference for the spec's `v1a` scheme.

version (unittest)
{
	private enum vecSigningKey = "whsk_6Xb/dCcHpPea21PS1N9VY/NZW723CEc77N4rJCubMbfVKIDij2HKpMKkioLlX0dRqSKJp4AJ6p9lMicMFs6Kvg==";
	private enum vecPublicKey = "whpk_1SiA4o9hyqTCpIqC5V9HUakiiaeACeqfZTInDBbOir4=";
	private enum vecSeedB64 = "6Xb/dCcHpPea21PS1N9VY/NZW723CEc77N4rJCubMbc=";
	private enum vecId = "msg_p5jXN8AQM9LWM0D4loKWxJek";
	private enum vecTimestamp = 1_614_265_330L;
	private enum vecPayload = `{"test": 2432232314}`;
	private enum vecSignature = "v1a,hnO3f9T8Ytu9HwrXslvumlUpqtNVqkhqw/enGzPCXe5BdqzCInXqYXFymVJaA7AZdpXwVLPo3mNl8EM+m7TBAg==";
}

/// sign() reproduces the official asymmetric reference vector exactly.
@safe unittest
{
	auto wh = AsymmetricWebhook(vecSigningKey);
	assert(wh.sign(vecId, vecTimestamp, vecPayload) == vecSignature);
}

/// A verify-only `whpk_` instance accepts the reference signature.
@safe unittest
{
	auto wh = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: vecSignature,
	];
	assert(wh.verifyAt(vecPayload, headers, vecTimestamp, false) == vecPayload);
}

/// A signing key verifies its own freshly produced signature end to end.
@safe unittest
{
	auto wh = AsymmetricWebhook(vecSigningKey);
	auto headers = wh.signHeaders(vecId, vecTimestamp, vecPayload);
	assert(wh.verifyAt(vecPayload, headers, vecTimestamp, false) == vecPayload);
}

/// fromSeed() reconstructs the same key pair as the serialised golden key.
@safe unittest
{
	auto seed = Base64.decode(vecSeedB64);
	auto wh = AsymmetricWebhook.fromSeed(seed);
	assert(wh.publicKeyEncoded() == vecPublicKey);
	assert(wh.sign(vecId, vecTimestamp, vecPayload) == vecSignature);
}

/// A signing key round-trips through its `whsk_` encoding.
@safe unittest
{
	auto wh = AsymmetricWebhook(vecSigningKey);
	assert(wh.signingKeyEncoded() == vecSigningKey);
}

/// fromRawPublicKey() builds a verify-only instance matching the golden key.
@safe unittest
{
	auto pk = Base64.decode(vecPublicKey[publicKeyPrefix.length .. $]);
	auto wh = AsymmetricWebhook.fromRawPublicKey(pk);
	assert(!wh.canSign());
	assert(wh.publicKeyEncoded() == vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: vecSignature,
	];
	assert(wh.verifyAt(vecPayload, headers, vecTimestamp, false) == vecPayload);
}

/// fromRawPublicKey() rejects a public key that is not 32 bytes.
@safe unittest
{
	import std.exception : collectException;

	ubyte[16] tooShort = 0;
	auto ex = collectException!WebhookException(AsymmetricWebhook.fromRawPublicKey(tooShort[]));
	assert(ex !is null && ex.error == WebhookError.invalidSecret);
}

/// fromRawSecretKey() builds a sign-and-verify instance matching the golden key.
@safe unittest
{
	auto sk = Base64.decode(vecSigningKey[signingKeyPrefix.length .. $]);
	auto wh = AsymmetricWebhook.fromRawSecretKey(sk);
	assert(wh.canSign());
	assert(wh.signingKeyEncoded() == vecSigningKey);
	assert(wh.publicKeyEncoded() == vecPublicKey);
	assert(wh.sign(vecId, vecTimestamp, vecPayload) == vecSignature);
}

/// fromRawSecretKey() rejects a secret key that is not 64 bytes.
@safe unittest
{
	import std.exception : collectException;

	ubyte[32] tooShort = 0;
	auto ex = collectException!WebhookException(AsymmetricWebhook.fromRawSecretKey(tooShort[]));
	assert(ex !is null && ex.error == WebhookError.invalidSecret);
}

/// canSign reflects whether a signing key is present.
@safe unittest
{
	assert(AsymmetricWebhook(vecSigningKey).canSign());
	assert(!AsymmetricWebhook(vecPublicKey).canSign());
}

/// A tampered signature does not verify (the final base64 char is flipped).
@safe unittest
{
	import std.exception : assertThrown;

	auto wh = AsymmetricWebhook(vecPublicKey);
	auto tampered = vecSignature[0 .. $ - 3] ~ "AAg==";
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: tampered,
	];
	assertThrown!WebhookException(wh.verifyAt(vecPayload, headers, vecTimestamp, false));
}

/// A tampered payload does not verify against a valid signature.
@safe unittest
{
	import std.exception : assertThrown;

	auto wh = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: vecSignature,
	];
	assertThrown!WebhookException(wh.verifyAt(`{"test": 2432232315}`, headers, vecTimestamp, false));
}

/// A valid `v1a` signature is found alongside a symmetric `v1` decoy entry.
@safe unittest
{
	auto wh = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: "v1,AAAA " ~ vecSignature,
	];
	assert(wh.verifyAt(vecPayload, headers, vecTimestamp, false) == vecPayload);
}

/// A different public key rejects an otherwise valid signature.
@safe unittest
{
	import std.exception : assertThrown;

	ubyte[seedBytes] otherSeed = 7;
	auto other = AsymmetricWebhook.fromSeed(otherSeed[]);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: vecSignature,
	];
	assertThrown!WebhookException(other.verifyAt(vecPayload, headers, vecTimestamp, false));
}

/// A verify-only instance cannot sign.
@safe unittest
{
	import std.exception : collectException;

	auto wh = AsymmetricWebhook(vecPublicKey);
	auto ex = collectException!WebhookException(wh.sign(vecId, vecTimestamp, vecPayload));
	assert(ex !is null && ex.error == WebhookError.signingKeyRequired);
}

/// A verify-only instance has no `whsk_` encoding to hand out.
@safe unittest
{
	import std.exception : collectException;

	auto wh = AsymmetricWebhook(vecPublicKey);
	auto ex = collectException!WebhookException(wh.signingKeyEncoded());
	assert(ex !is null && ex.error == WebhookError.signingKeyRequired);
}

/// An unrecognised key prefix is rejected.
@safe unittest
{
	import std.exception : collectException;

	auto ex = collectException!WebhookException(
			AsymmetricWebhook("whsec_MfKQ9r8GKYqrTwjUPD8ILPZIo2LaLaSw"));
	assert(ex !is null && ex.error == WebhookError.invalidSecret);
}

/// A `whpk_` key of the wrong length is rejected.
@safe unittest
{
	import std.exception : collectException;

	auto ex = collectException!WebhookException(AsymmetricWebhook("whpk_AAAA"));
	assert(ex !is null && ex.error == WebhookError.invalidSecret);
}

/// An empty key is rejected.
@safe unittest
{
	import std.exception : collectException;

	auto ex = collectException!WebhookException(AsymmetricWebhook(""));
	assert(ex !is null && ex.error == WebhookError.emptySecret);
}

/// A timestamp outside tolerance is rejected even with a valid signature.
@safe unittest
{
	import std.exception : collectException;

	auto wh = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: vecSignature,
	];
	auto ex = collectException!WebhookException(wh.verifyAt(vecPayload,
			headers, vecTimestamp + 301, true));
	assert(ex !is null && ex.error == WebhookError.timestampTooOld);
}

/// Svix-branded header aliases are accepted as a fallback.
@safe unittest
{
	auto wh = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		"svix-id": vecId, "svix-timestamp": vecTimestamp.to!string,
		"svix-signature": vecSignature,
	];
	assert(wh.verifyAt(vecPayload, headers, vecTimestamp, false) == vecPayload);
}

/// A signature carrying base64URL alphabet characters (`-`/`_`) is rejected
/// rather than mis-decoded: verifyDetached fails the standard-base64 decode and
/// returns false, so verification throws.
@safe unittest
{
	import std.exception : assertThrown;

	auto wh = AsymmetricWebhook(vecPublicKey);
	// The genuine signature with two standard-base64 chars swapped for their
	// base64URL equivalents, so a strict decoder must reject it.
	auto urlEncoded = asymmetricVersion ~ ",hnO3f9T8Ytu9HwrXslvumlUpqtNVqkhqw_enGzPCXe5Bdqz"
		~ "CInXqYXFymVJaA7AZdpXwVLPo3mNl8EM-m7TBAg==";
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: urlEncoded,
	];
	assertThrown!WebhookException(wh.verifyAt(vecPayload, headers, vecTimestamp, false));
}

/// Signing and verification work without an eager module ctor: libsodium is
/// initialised lazily on the first crypto call.
@safe unittest
{
	auto wh = AsymmetricWebhook(vecSigningKey);
	auto headers = wh.signHeaders(vecId, vecTimestamp, vecPayload);
	assert(wh.verifyAt(vecPayload, headers, vecTimestamp, false) == vecPayload);
}

/// fromSeed() derives the golden public key from its 32-byte seed.
@safe unittest
{
	auto seed = Base64.decode(vecSeedB64);
	auto wh = AsymmetricWebhook.fromSeed(seed);
	assert(wh.publicKeyEncoded() == vecPublicKey);
}

/// The public verify() uses the real clock: a payload signed at the current time
/// passes without an injected `now`.
@safe unittest
{
	import std.datetime.systime : Clock;
	import std.datetime.timezone : UTC;

	auto wh = AsymmetricWebhook(vecSigningKey);
	const now = Clock.currTime(UTC()).toUnixTime();
	auto headers = wh.signHeaders(vecId, now, vecPayload);
	assert(wh.verify(vecPayload, headers) == vecPayload);
}

/// The public verify() rejects a payload whose timestamp is well outside the
/// tolerance window of the real clock.
@safe unittest
{
	import std.datetime.systime : Clock;
	import std.datetime.timezone : UTC;
	import std.exception : collectException;

	auto wh = AsymmetricWebhook(vecSigningKey);
	const old = Clock.currTime(UTC()).toUnixTime() - 1000;
	auto headers = wh.signHeaders(vecId, old, vecPayload);
	auto ex = collectException!WebhookException(wh.verify(vecPayload, headers));
	assert(ex !is null && ex.error == WebhookError.timestampTooOld);
}

/// A `whsk_` signing key of the wrong length is rejected.
@safe unittest
{
	import std.exception : collectException;

	auto ex = collectException!WebhookException(AsymmetricWebhook("whsk_AAAA"));
	assert(ex !is null && ex.error == WebhookError.invalidSecret);
}

/// fromSeed() rejects a seed that is not 32 bytes.
@safe unittest
{
	import std.exception : collectException;

	ubyte[16] shortSeed = 0;
	auto ex = collectException!WebhookException(AsymmetricWebhook.fromSeed(shortSeed[]));
	assert(ex !is null && ex.error == WebhookError.invalidSecret);
}

/// verify() rejects headers missing a required entry.
@safe unittest
{
	import std.exception : collectException;

	auto wh = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [headerId: vecId, headerSignature: vecSignature,];
	auto ex = collectException!WebhookException(wh.verify(vecPayload, headers));
	assert(ex !is null && ex.error == WebhookError.missingHeaders);
}

/// An unpadded (non-canonical) signature is rejected: the spec mandates standard
/// padded base64 for `v1a`, matching `v1`, so a stripped-padding signature must
/// fail verification rather than be silently re-padded.
@safe unittest
{
	import std.algorithm.searching : endsWith;
	import std.exception : assertThrown;

	auto wh = AsymmetricWebhook(vecPublicKey);
	auto unpadded = vecSignature;
	while (unpadded.endsWith("="))
		unpadded = unpadded[0 .. $ - 1];
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: unpadded,
	];
	assertThrown!WebhookException(wh.verifyAt(vecPayload, headers, vecTimestamp, false));
}

/// tryVerify reports success with the payload for a valid v1a signature.
@safe unittest
{
	auto wh = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: vecSignature,
	];
	auto result = wh.tryVerifyAt(vecPayload, headers, vecTimestamp, false);
	assert(result.ok);
	assert(result.payload == vecPayload);
}

/// tryVerify reports failure (without throwing) for a tampered payload, naming
/// noMatch as the cause.
@safe unittest
{
	auto wh = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: vecSignature,
	];
	auto result = wh.tryVerifyAt(`{"test": 2432232315}`, headers, vecTimestamp, false);
	assert(!result.ok);
	assert(result.error == WebhookError.noMatch);
}

/// tryVerify reports missingHeaders without throwing when a header is absent.
@safe unittest
{
	auto wh = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [headerId: vecId, headerSignature: vecSignature];
	auto result = wh.tryVerifyAt(vecPayload, headers, vecTimestamp, false);
	assert(!result.ok);
	assert(result.error == WebhookError.missingHeaders);
}

/// tryVerify reports timestampTooOld without throwing for a stale timestamp.
@safe unittest
{
	auto wh = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: vecSignature,
	];
	auto result = wh.tryVerifyAt(vecPayload, headers, vecTimestamp + 301, true);
	assert(!result.ok);
	assert(result.error == WebhookError.timestampTooOld);
}

/// The public tryVerify uses the real clock: a payload signed now succeeds.
@safe unittest
{
	import std.datetime.systime : Clock;
	import std.datetime.timezone : UTC;

	auto wh = AsymmetricWebhook(vecSigningKey);
	const now = Clock.currTime(UTC()).toUnixTime();
	auto headers = wh.signHeaders(vecId, now, vecPayload);
	auto result = wh.tryVerify(vecPayload, headers);
	assert(result.ok);
	assert(result.payload == vecPayload);
}

/// The throwing verify() is built on tryVerify: when tryVerify fails, verify()
/// throws an exception carrying the same WebhookError cause.
@safe unittest
{
	import std.exception : collectException;

	auto wh = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: vecSignature,
	];
	auto fromTry = wh.tryVerifyAt(`{"test": 2432232315}`, headers, vecTimestamp, false);
	auto ex = collectException!WebhookException(wh.verifyAt(`{"test": 2432232315}`,
			headers, vecTimestamp, false));
	assert(!fromTry.ok);
	assert(ex !is null && ex.error == fromTry.error);
}

/// A freshly signed payload round-trips through verify, confirming the ed25519
/// primitives operate normally even though fromSeed wipes its transient secret-key
/// stack buffer after copying the key into the struct.
@safe unittest
{
	auto signer = AsymmetricWebhook(vecSigningKey);
	auto sig = signer.sign(vecId, vecTimestamp, vecPayload);
	auto verifier = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: sig,
	];
	assert(verifier.verifyAt(vecPayload, headers, vecTimestamp, false) == vecPayload);
}

/// withTolerance returns a copy whose toleranceSeconds is the supplied value.
@safe unittest
{
	auto wh = AsymmetricWebhook(vecSigningKey).withTolerance(600);
	assert(wh.toleranceSeconds == 600);
}

/// withTolerance leaves the source instance's tolerance untouched.
@safe unittest
{
	auto wh = AsymmetricWebhook(vecSigningKey);
	const widened = wh.withTolerance(600);
	assert(wh.toleranceSeconds == defaultToleranceSeconds);
	assert(widened.toleranceSeconds == 600);
}

/// The copy shares the key bytes, so a fluently-widened instance still signs and
/// verifies end to end.
@safe unittest
{
	auto wh = AsymmetricWebhook(vecSigningKey).withTolerance(600);
	auto headers = wh.signHeaders(vecId, vecTimestamp, vecPayload);
	assert(wh.verifyAt(vecPayload, headers, vecTimestamp, false) == vecPayload);
}

/// A widened tolerance lets an otherwise-stale timestamp verify, proving the
/// copied toleranceSeconds is the value verification consults.
@safe unittest
{
	import std.datetime.systime : Clock;
	import std.datetime.timezone : UTC;

	const old = Clock.currTime(UTC()).toUnixTime() - 1000;
	auto wh = AsymmetricWebhook(vecSigningKey).withTolerance(2000);
	auto headers = wh.signHeaders(vecId, old, vecPayload);
	assert(wh.verify(vecPayload, headers) == vecPayload);
}

/// withTolerance preserves verify-only status: a `whpk_` copy cannot sign.
@safe unittest
{
	auto wh = AsymmetricWebhook(vecPublicKey).withTolerance(600);
	assert(!wh.canSign());
}

// --- Dual-scheme verification tests -----------------------------------------
// A receiver that accepts both schemes holds a symmetric secret and a
// verify-only public key; verifyAny tries each.

version (unittest)
{
	private enum vecSecret = "whsec_MfKQ9r8GKYqrTwjUPD8ILPZIo2LaLaSw";
}

/// verifyAny accepts a payload carrying a symmetric `v1` signature.
@safe unittest
{
	auto symmetric = Webhook(vecSecret);
	auto asymmetric = AsymmetricWebhook(vecPublicKey);
	auto headers = symmetric.signHeaders(vecId, vecTimestamp, vecPayload);
	assert(verifyAnyAt(symmetric, asymmetric, vecPayload, headers,
			vecTimestamp, false) == vecPayload);
}

/// verifyAny accepts a payload carrying an asymmetric `v1a` signature.
@safe unittest
{
	auto symmetric = Webhook(vecSecret);
	auto asymmetric = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: vecSignature,
	];
	assert(verifyAnyAt(symmetric, asymmetric, vecPayload, headers,
			vecTimestamp, false) == vecPayload);
}

/// verifyAny rejects a payload that matches neither scheme.
@safe unittest
{
	import std.exception : collectException;

	auto symmetric = Webhook(vecSecret);
	auto asymmetric = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: "v1,AAAA",
	];
	auto ex = collectException!WebhookException(verifyAnyAt(symmetric,
			asymmetric, vecPayload, headers, vecTimestamp, false));
	assert(ex !is null && ex.error == WebhookError.noMatch);
}

/// verifyAny enforces the timestamp window: an in-tolerance asymmetric payload
/// passes while an out-of-tolerance one is rejected.
@safe unittest
{
	import std.exception : collectException;

	auto symmetric = Webhook(vecSecret);
	auto asymmetric = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: vecSignature,
	];
	assert(verifyAnyAt(symmetric, asymmetric, vecPayload, headers, vecTimestamp, true) == vecPayload);
	auto ex = collectException!WebhookException(verifyAnyAt(symmetric,
			asymmetric, vecPayload, headers, vecTimestamp + 301, true));
	assert(ex !is null && ex.error == WebhookError.timestampTooOld);
}

/// The public verifyAny uses the real clock: a freshly signed asymmetric
/// payload passes without an injected `now`.
@safe unittest
{
	import std.datetime.systime : Clock;
	import std.datetime.timezone : UTC;

	auto signer = AsymmetricWebhook(vecSigningKey);
	auto symmetric = Webhook(vecSecret);
	auto asymmetric = AsymmetricWebhook(vecPublicKey);
	const now = Clock.currTime(UTC()).toUnixTime();
	auto headers = signer.signHeaders(vecId, now, vecPayload);
	assert(verifyAny(symmetric, asymmetric, vecPayload, headers) == vecPayload);
}

/// verifyAnyIgnoringTimestamp accepts an old asymmetric payload that the
/// timestamp-checking path would reject.
@safe unittest
{
	auto symmetric = Webhook(vecSecret);
	auto asymmetric = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: vecSignature,
	];
	assert(verifyAnyIgnoringTimestamp(symmetric, asymmetric, vecPayload, headers) == vecPayload);
}

/// verifyAny surfaces a symmetric invalidTolerance config fault rather than
/// masking it behind the asymmetric verifier's noMatch.
@safe unittest
{
	import std.exception : collectException;

	auto symmetric = Webhook(vecSecret).withTolerance(0);
	auto asymmetric = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: "v1,AAAA",
	];
	auto ex = collectException!WebhookException(verifyAnyAt(symmetric,
			asymmetric, vecPayload, headers, vecTimestamp, true));
	assert(ex !is null && ex.error == WebhookError.invalidTolerance);
}

/// tryVerifyAny reports success with the payload for an asymmetric `v1a`
/// signature, without throwing.
@safe unittest
{
	auto symmetric = Webhook(vecSecret);
	auto asymmetric = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: vecSignature,
	];
	auto result = tryVerifyAnyAt(symmetric, asymmetric, vecPayload, headers, vecTimestamp, false);
	assert(result.ok);
	assert(result.payload == vecPayload);
}

/// tryVerifyAny reports failure (without throwing) for a payload matching
/// neither scheme, naming noMatch as the cause.
@safe unittest
{
	auto symmetric = Webhook(vecSecret);
	auto asymmetric = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: "v1,AAAA",
	];
	auto result = tryVerifyAnyAt(symmetric, asymmetric, vecPayload, headers, vecTimestamp, false);
	assert(!result.ok);
	assert(result.error == WebhookError.noMatch);
}

/// The public tryVerifyAny uses the real clock: a freshly signed asymmetric
/// payload succeeds without an injected `now`.
@safe unittest
{
	import std.datetime.systime : Clock;
	import std.datetime.timezone : UTC;

	auto signer = AsymmetricWebhook(vecSigningKey);
	auto symmetric = Webhook(vecSecret);
	auto asymmetric = AsymmetricWebhook(vecPublicKey);
	const now = Clock.currTime(UTC()).toUnixTime();
	auto headers = signer.signHeaders(vecId, now, vecPayload);
	auto result = tryVerifyAny(symmetric, asymmetric, vecPayload, headers);
	assert(result.ok);
	assert(result.payload == vecPayload);
}

/// tryVerifyAnyIgnoringTimestamp accepts an old asymmetric payload that the
/// timestamp-checking path would reject.
@safe unittest
{
	auto symmetric = Webhook(vecSecret);
	auto asymmetric = AsymmetricWebhook(vecPublicKey);
	string[string] headers = [
		headerId: vecId, headerTimestamp: vecTimestamp.to!string,
		headerSignature: vecSignature,
	];
	auto result = tryVerifyAnyIgnoringTimestamp(symmetric, asymmetric, vecPayload, headers);
	assert(result.ok);
	assert(result.payload == vecPayload);
}

// --- v2a tests ----------------------------------------------------------------
// Vectors from the specification (standard-webhooks.md, "Asymmetric signatures",
// and extensions/endpoint-verification.md, "Examples").

version (unittest)
{
	private enum v2SecretKey = "whsk_4uKPjji/dhB8w6GW3YYDnIMYvXcdHrvH6lidTr4Z+EY=";
	private enum v2PublicKey = "whpk_uWKK13PfwqyOgrqT0OrWKcS2uVD7e89+oUKnkoPjx7w=";
	private enum v2EndpointId = "ep_2fVZdC8Kx9TR4ZoCqHWt3NnLgRb";
	private enum v2Id = "msg_2KWPBgLlAfxdpx2AI54pPJ85f4W";
	private enum v2Timestamp = 1_674_087_231L;
	private enum v2Payload = `{"type":"contact.created","timestamp":"2022-11-03T20:26:10.344522Z","data":{"id":"1f81eb52-5198-4599-803e-771906343485"}}`;
	private enum v2Hash = "YXCi5iN+rjB+iEb6bvg1XbWbVBL+r2S+as3k3n1Ih/A=";
	private enum v2Signature = "v2a,kG9XaxZjAEpKB8KeQQb5G1Xp73YH5Rf5gxoWe7cg1kYMiyspdtZXe9w+dAwKeOurAwxfqmlOG/QR4m9s37DzAg==";
	private enum v2Challenge = "0njH7N3kV5eXPB+/eh+eoA2Ahvz2JgNp0iC/BLOl6yM=";
	private enum v2ChallengeResponse = "v2a,t0RDFhzk7OtVzgvMsjuXnodSWuby2BVX+zPqw2/ksUk=";

	private string[string] v2Headers(string signature = v2Signature)
	{
		return [
			headerId: v2Id,
			headerTimestamp: v2Timestamp.to!string,
			headerSignature: signature,
		];
	}
}

/// The signed-content hash and signature match the spec's example exactly.
@safe unittest
{
	auto hash = asymmetricSignedContentHash(v2EndpointId, v2Id, v2Timestamp, v2Payload);
	assert(Base64.encode(hash[]) == v2Hash);

	auto signer = AsymmetricSigner(v2SecretKey);
	assert(signer.publicKeyEncoded() == v2PublicKey);
	assert(signer.signingKeyEncoded() == v2SecretKey);
	assert(signer.sign(v2EndpointId, v2Id, v2Timestamp, v2Payload) == v2Signature);
}

/// The spec's example signature verifies for its endpoint, and not for another.
@safe unittest
{
	auto verifier = AsymmetricVerifier(v2EndpointId, v2PublicKey);
	assert(verifier.endpointId == v2EndpointId);
	assert(verifier.tryVerifyAt(v2Payload, v2Headers(), v2Timestamp, true).ok);
	assert(verifier.verifyIgnoringTimestamp(v2Payload, v2Headers()) == v2Payload);

	auto other = AsymmetricVerifier("ep_other", v2PublicKey);
	auto result = other.tryVerifyAt(v2Payload, v2Headers(), v2Timestamp, true);
	assert(!result.ok && result.error == WebhookError.noMatch);
}

/// Timestamp tolerance applies as in the other schemes.
@safe unittest
{
	auto verifier = AsymmetricVerifier(v2EndpointId, v2PublicKey);
	auto result = verifier.tryVerifyAt(v2Payload, v2Headers(), v2Timestamp + 301, true);
	assert(!result.ok && result.error == WebhookError.timestampTooOld);
	assert(verifier.tryVerifyAt(v2Payload, v2Headers(), v2Timestamp + 301, false).ok);
}

/// A tampered payload or signature fails; v1a/v1 entries are skipped, and a v2a
/// entry among them still matches.
@safe unittest
{
	auto verifier = AsymmetricVerifier(v2EndpointId, v2PublicKey);
	assert(!verifier.tryVerifyAt(v2Payload ~ " ", v2Headers(), v2Timestamp, true).ok);
	assert(!verifier.tryVerifyAt(v2Payload,
			v2Headers(v2Signature[0 .. $ - 4] ~ "AAg=="), v2Timestamp, true).ok);
	assert(!verifier.tryVerifyAt(v2Payload,
			v2Headers("v1a" ~ v2Signature[3 .. $]), v2Timestamp, true).ok);
	assert(verifier.tryVerifyAt(v2Payload,
			v2Headers("v1,K5oZfzN95Z9UVu1EsfQmfVNQhnkZ2pj9o9NDN/H/pI4= " ~ v2Signature),
			v2Timestamp, true).ok);
}

/// Any trusted key verifies, so consumers can rotate keys.
@safe unittest
{
	auto newSigner = AsymmetricSigner.fromSeed(new ubyte[32]);
	auto verifier = AsymmetricVerifier(v2EndpointId, newSigner.publicKeyEncoded(), v2PublicKey);
	assert(verifier.tryVerifyAt(v2Payload, v2Headers(), v2Timestamp, true).ok);

	auto sig = newSigner.sign(v2EndpointId, v2Id, v2Timestamp, v2Payload);
	assert(verifier.tryVerifyAt(v2Payload, v2Headers(sig), v2Timestamp, true).ok);
	assert(!AsymmetricVerifier(v2EndpointId, v2PublicKey)
			.tryVerifyAt(v2Payload, v2Headers(sig), v2Timestamp, true).ok);
}

/// signHeaders round-trips through the verifier.
@safe unittest
{
	auto signer = AsymmetricSigner(v2SecretKey);
	auto headers = signer.signHeaders(v2EndpointId, v2Id, v2Timestamp, v2Payload);
	assert(headers[headerSignature] == v2Signature);
	assert(AsymmetricVerifier(v2EndpointId, v2PublicKey).tryVerifyAt(v2Payload,
			headers, v2Timestamp, true).ok);
}

/// The 64-byte `seed ‖ public_key` whsk_ form of AsymmetricWebhook is accepted,
/// and normalised to the spec's 32-byte seed form; a mismatched public half is
/// rejected.
@safe unittest
{
	import std.exception : collectException;

	auto legacy = AsymmetricWebhook.fromSeed(Base64.decode(v2SecretKey[5 .. $]));
	auto signer = AsymmetricSigner(legacy.signingKeyEncoded());
	assert(signer.signingKeyEncoded() == v2SecretKey);
	assert(signer.sign(v2EndpointId, v2Id, v2Timestamp, v2Payload) == v2Signature);

	auto bytes = Base64.decode(legacy.signingKeyEncoded()[5 .. $]);
	bytes[$ - 1] ^= 1;
	auto ex = collectException!WebhookException(
			AsymmetricSigner("whsk_" ~ Base64.encode(bytes).idup));
	assert(ex !is null && ex.error == WebhookError.invalidSecret);
}

/// Construction rejects bad endpoint IDs and keys.
@safe unittest
{
	import std.exception : collectException;

	WebhookError errorOf(lazy AsymmetricVerifier v)
	{
		auto ex = collectException!WebhookException(v);
		assert(ex !is null);
		return ex.error;
	}

	assert(errorOf(AsymmetricVerifier("", v2PublicKey)) == WebhookError.invalidEndpointId);
	assert(errorOf(AsymmetricVerifier("ep.1", v2PublicKey)) == WebhookError.invalidEndpointId);
	assert(errorOf(AsymmetricVerifier(v2EndpointId)) == WebhookError.emptySecret);
	assert(errorOf(AsymmetricVerifier(v2EndpointId,
			v2PublicKey[5 .. $])) == WebhookError.invalidSecret);
	assert(errorOf(AsymmetricVerifier(v2EndpointId, "whpk_AAAA")) == WebhookError.invalidSecret);
	assert(errorOf(AsymmetricVerifier(v2EndpointId, v2SecretKey)) == WebhookError.invalidSecret);

	auto ex = collectException!WebhookException(AsymmetricSigner(v2SecretKey)
			.sign("ep.1", v2Id, v2Timestamp, v2Payload));
	assert(ex !is null && ex.error == WebhookError.invalidEndpointId);

	ex = collectException!WebhookException(AsymmetricSigner(v2PublicKey));
	assert(ex !is null && ex.error == WebhookError.invalidSecret);

	AsymmetricSigner empty;
	ex = collectException!WebhookException(empty.sign(v2EndpointId, v2Id, v2Timestamp, v2Payload));
	assert(ex !is null && ex.error == WebhookError.signingKeyRequired);
}

/// HSM flow: hash, sign elsewhere, format. Public keys format from raw or SPKI.
@safe unittest
{
	import std.exception : collectException;

	auto raw = Base64.decode(v2Signature[4 .. $]);
	assert(formatAsymmetricSignature(raw) == v2Signature);
	assert(collectException!WebhookException(formatAsymmetricSignature(raw[0 .. 63])) !is null);

	auto pk = Base64.decode(v2PublicKey[5 .. $]);
	assert(formatAsymmetricPublicKey(pk) == v2PublicKey);
	assert(formatAsymmetricPublicKey(ed25519SpkiPrefix[] ~ pk) == v2PublicKey);
	auto badSpki = ed25519SpkiPrefix[].dup ~ pk;
	badSpki[0] = 0;
	assert(collectException!WebhookException(formatAsymmetricPublicKey(badSpki)) !is null);

	assert(AsymmetricVerifier.fromRawPublicKeys(v2EndpointId, pk)
			.tryVerifyAt(v2Payload, v2Headers(), v2Timestamp, true).ok);
}

/// Endpoint verification: the spec's asymmetric example vector, verified against
/// any trusted key and rejected otherwise.
@safe unittest
{
	auto verifier = AsymmetricVerifier(v2EndpointId, v2PublicKey);
	assert(verifier.endpointVerificationResponse(v2Challenge) == v2ChallengeResponse);
	assert(verifier.isValidEndpointVerificationResponse(v2Challenge, v2ChallengeResponse));
	verifier.verifyEndpointVerificationResponse(v2Challenge, v2ChallengeResponse);

	assert(!verifier.isValidEndpointVerificationResponse("wrong-challenge", v2ChallengeResponse));
	assert(!verifier.isValidEndpointVerificationResponse(v2Challenge,
			"v2,abc " ~ v2ChallengeResponse));
	assert(!AsymmetricVerifier("ep_other", v2PublicKey)
			.isValidEndpointVerificationResponse(v2Challenge, v2ChallengeResponse));

	// A rotated-in key answers with the newest key; the producer accepts any.
	auto newer = AsymmetricSigner.fromSeed(new ubyte[32]).publicKeyEncoded();
	auto rotated = AsymmetricVerifier(v2EndpointId, newer, v2PublicKey);
	assert(rotated.endpointVerificationResponse(v2Challenge) != v2ChallengeResponse);
	assert(rotated.isValidEndpointVerificationResponse(v2Challenge, v2ChallengeResponse));
}
