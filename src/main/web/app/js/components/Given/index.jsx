import React from 'react'
import GivenLine from './GivenLine'
import RAddGiven from '../../containers/RGiven/RAddGiven'
import CentredButton from '../CentredButton'

const Given = ({ given, onFinishClick, complete }) => (
  <div className={ ["panel", "panel-default", complete ? "panel-success" : ""].join(" ") }>
    <div className="panel-heading">
      <h3 className="panel-title pull-left">Given</h3>
      <div className="clearfix" />
    </div>
    <ul className="list-group">
      {given.map((g, i) => <GivenLine key={i} lineNo={g.lineNo} body={g.body} />)}
    </ul>
    { complete ? null : (
      <div className="panel-body">
        <RAddGiven />
        <CentredButton onButtonClick={(e) => { onFinishClick(); e.preventDefault() }} text="Finish" />
      </div>)}
  </div>
)

export default Given

