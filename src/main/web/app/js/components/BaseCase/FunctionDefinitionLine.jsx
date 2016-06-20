import React from 'react'

const FunctionDefinitionLine = ({ body }) => (
  <tr>
    <td className="col-sm-7">= { body }</td>
    <td className="col-sm-5">by function def.</td>
  </tr>
)

export default FunctionDefinitionLine

