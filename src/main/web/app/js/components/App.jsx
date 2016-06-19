import React from 'react'
import AppRow from './AppRow'
import RFunctionInput from '../containers/RFunctionInput'
import RToShow from '../containers/RToShow' 
import RGiven from '../containers/RGiven'
import RProof from '../containers/RProof'
import RBaseCase from '../containers/RBaseCase'
import RInductiveCase from '../containers/RInductiveCase'
import { PROOF_MODE } from '../constants'

const App = ({ showGiven, showProof, mode }) => (
  <div className="container">
    <AppRow rowClass="top-buffer"><RToShow /></AppRow>
    { showGiven ? (<AppRow><RGiven /></AppRow>) : null }
    { showProof && mode == PROOF_MODE.DIRECT ? (<AppRow><RProof /></AppRow>) : null }
    { showProof && mode == PROOF_MODE.INDUCTION ? 
      (<AppRow><RBaseCase /></AppRow>) : null }
    { showProof && mode == PROOF_MODE.INDUCTION ? 
      (<AppRow><RInductiveCase /></AppRow>) : null }
  </div>
)

export default App

