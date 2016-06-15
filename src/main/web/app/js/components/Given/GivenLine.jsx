import React from 'react'

const GivenLine = ({ lineNo, body }) => (
  <li className="list-group-item">({ lineNo }) { body }</li>
)

export default GivenLine

