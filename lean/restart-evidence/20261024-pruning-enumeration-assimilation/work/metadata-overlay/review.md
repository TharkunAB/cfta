# Unused written witness metadata override

Recorded at 2026-10-24T18:49:09.050296+02:00. The original frozen owner remains byte-exact. Root found this metadata issue during source-only review before the body gate. No compiler or body failure occurred.

The overlay changes only two metadata values in obtain-fields.json: written.used becomes false, and skipped_fields records that same written Success witness with its unchanged exact type and the reason it is unused. The raw suffix proof computes finish directly. middleSame, middleStored and middleRealized still supply the actual endpoint, target readback and all-slot realization. The unused witness remains obtained and typed; it is not deleted or misreported as consumed.

The override binds the original FROZEN, pins and metadata file hashes. The exact unified patch and effective metadata are retained. Every public/local header, scoped type, action, case, instance, count and source object stays unchanged. All58 original payload hashes were verified before and after creating this separate overlay. Root must accept this override explicitly before the body gate. Guard provides independent review.
