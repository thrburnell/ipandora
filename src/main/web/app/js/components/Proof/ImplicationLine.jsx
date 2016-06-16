import React from 'react'

const ImplicationLine = ({ lineNo, body, justification }) => (
  <li className="list-group-item">({ lineNo }) { body }       by justification</li>
)

export default ImplicationLine

