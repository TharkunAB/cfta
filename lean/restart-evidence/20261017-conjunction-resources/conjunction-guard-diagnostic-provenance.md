# Auxiliary diagnostic provenance

Two auxiliary instance-resolution commands used /tmp/guard-instance.lean.
They were not production, public, or integration validation runs.
The first command used namespace Probe. Its source is reconstructed exactly
from the tool command in conjunction-guard-diagnostic-1.reconstructed.lean.
The second command changed that namespace to MicroCFTA.Probe in place.
Its retained scratch bytes are conjunction-guard-diagnostic-2.source.lean.
The commands reported namespace errors and then instance-resolution errors.
Their output is retained in the tool transcript. No separate original raw
log file was created for those two scratch commands. They are not counted
as successful checks. Production attempts and all public/kernel attempts
have distinct exact snapshots and raw log files.
