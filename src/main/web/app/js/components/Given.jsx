import React from 'react'

const GivenLine = ({ lineNo, body }) => (
  <li className="list-group-item">({ lineNo }) { body }</li>
)

const Given = ({ given }) => (
  <div className="panel panel-default">
    <div className="panel-heading">
      <h3 className="panel-title pull-left">Given</h3>
      <div className="clearfix" />
    </div>
    <ul className="list-group">
      {given.map(g => <GivenLine lineNo={g.lineNo} body={g.body} />)}
    </ul>
    <div className="panel-body">
      Givens will go here
    </div>
  </div>
)

export default Given

