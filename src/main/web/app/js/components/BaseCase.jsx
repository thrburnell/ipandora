import React from 'react'

const BaseCase = ({ active=false, toShow }) => {
  if (!active) {
    return null
  }

  return (
    <div className="panel panel-default">
      <div className="panel-heading">
        <h3 className="panel-title">Base Case</h3>
      </div>
      <ul className="list-group">
        <li className="list-group-item">
          <strong>To Show: </strong>
          { toShow }
        </li>
      </ul>
      <div className="panel-body">
        Proof steps here...
      </div>
    </div>
  )
}

export default BaseCase

