theorem IsolatedPending.through_frame
    (isolated : IsolatedPending held handle before) (frame : Frame before after) :
    IsolatedPending held handle after := by
