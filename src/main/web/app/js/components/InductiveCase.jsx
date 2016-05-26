import React from 'react'

const InductiveCase = (props) => {

  if (!props.active) {
    return null
  }

  return (
    <div className="panel panel-default">
      <div className="panel-heading">
        <h3 className="panel-title">Inductive Case</h3>
      </div>
      <ul className="list-group">
        <li className="list-group-item">
          Take an arbitrary <strong>{ props.arbitrary.name }</strong> in <strong>{ props.arbitrary.domain }</strong>
        </li>
        <li className="list-group-item">
          <strong>Inductive Hypothesis: </strong>
          { props.hypothesis }
        </li>
        <li className="list-group-item">
          <strong>To Show: </strong>
          { props.toShow }
        </li>
      </ul>
      <div className="panel-body">
        Proof steps here...
      </div>
    </div>
  )
}

export default InductiveCase

