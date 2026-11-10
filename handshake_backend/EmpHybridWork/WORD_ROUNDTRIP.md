# Full-word private roundtrip

`word-roundtrip-report.json` passes a native field arithmetic→EMP255-bit→native field roundtrip. One checked512-pair pool supplies255 distinct masks in each direction, under operation0/FieldToBoolean then operation1/BooleanToField. The decoded word remains authenticated/private in EMP; its reverse masked XOR opens only uniform masked bits. The rebuilt native word is checked equal to the original native value by opening only a zero predicate. Independent EMP comparison with the disposable public fixture expectation also succeeds.

The second control supplies a wrong operation counter only on B. Collective readiness rejects before the reverse masked opening, poisons the pool on both sides and closes without a successful fixture result. Both groups are terminal/reaped. This extends the earlier one-direction controls; it is not X25519, Signal/TLS, remote identity authentication, erasure or a malicious-composition proof.

The exact public512/B5/C2 profile passes the same rational S40 bound check as the earlier profiles;1024/B5/C2 is also calculated for the next bounded curve control. `curve-parameters.json` is only public combinatorial evidence. No statistical parameter or compute corruption threshold changes.
