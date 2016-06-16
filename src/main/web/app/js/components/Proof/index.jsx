import React from 'react'
import CentredButton from '../CentredButton'
import ProofStepSelector from './ProofStepSelector'
import RAssertLine from '../../containers/RProof/RAssertLine'

const Proof = ({ lines, complete }) => (
  <div className="panel panel-default">
    <div className="panel-heading">
      <h3 className="panel-title pull-left">Proof</h3>
      <div className="clearfix" />
    </div>
    <ul className="list-group">
      {lines.map((g, i) => null)}
    </ul>
    { complete ? null : (
      <div className="panel-footer text-center">
        <ProofStepSelector 
         onAssertClick={() => console.log('Assert')}
         onAssumeClick={() => console.log('Assume')}
         onTakeArbitraryClick={() => console.log('Take arbitrary')}
         onCaseAnalysisClick={() => console.log('Case analysis')}/>
      </div>)}
  </div>
)

export default Proof

