import React from 'react'

const ImplicationLine = ({ lineNo, body, justification, selectable, onSelect }) => (
  <tr>
    <td className="col-sm-1 text-center">({ lineNo })</td>
    <td className="col-sm-6">{ body }</td>
    <td className="col-sm-4">{ justification }</td>
    <td className="col-sm-1 text-center">
      { selectable ? <input type="checkbox" onClick={ onSelect }/> : null }
    </td>
  </tr>
)

export default ImplicationLine

