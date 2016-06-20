import React from 'react'

const InductiveHypothesisLine = ({ body }) => (
  <tr>
    <td className="col-sm-7">= { body }</td>
    <td className="col-sm-5">by ind. hyp.</td>
  </tr>
)

export default InductiveHypothesisLine

