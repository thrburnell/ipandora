import React from 'react'

const GivenLine = ({ lineNo, body, selectable, onSelect }) => (
  <tr>
    <td className="col-sm-1 text-center">({ lineNo })</td>
    <td className="col-sm-10">{ body }</td>
    <td className="col-sm-1 text-center">
      { selectable ? <input type="checkbox" onClick={ onSelect }/> : null }
    </td>
  </tr>
)

export default GivenLine

