The root sent the V2 review requests with send_message after the reviewer task completed.
send_message queued the requests but did not start a new turn.
A live-agent query then showed the reviewer task as completed.
The root used followup_task to start the V2 review with the complete current request.
No V2 review or compiler result was claimed from the queued requests.
No compiler or metadata job was restarted. Strict1 remained terminal and preserved.
This dispatch error caused a wait. It did not change the source or proof evidence.
