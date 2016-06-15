import React from 'react'
import GivenLine from './GivenLine'
import RAddGiven from '../../containers/RGiven/RAddGiven'

const Given = ({ given }) => (
  <div className="panel panel-default">
    <div className="panel-heading">
      <h3 className="panel-title pull-left">Given</h3>
      <div className="clearfix" />
    </div>
    <ul className="list-group">
      {given.map((g, i) => <GivenLine key={i} lineNo={g.lineNo} body={g.body} />)}
    </ul>
    <div className="panel-body">
      <RAddGiven />
    </div>
  </div>
)

export default Given

