import React from 'react'
import AppRow from './AppRow'
import RFunctionInput from '../containers/RFunctionInput'
import RToShow from '../containers/RToShow' 
import RGiven from '../containers/RGiven'
import RProof from '../containers/RProof'
import RBaseCase from '../containers/RBaseCase'
import RInductiveCase from '../containers/RInductiveCase'

const App = ({ showGiven, showFnInput, showDirectProof, showInductiveProof }) => (
  <div className="container">
    <AppRow rowClass="top-buffer"><RToShow /></AppRow>
    { showGiven ? (<AppRow><RGiven /></AppRow>) : null }
    { showFnInput ? (<AppRow><RFunctionInput /></AppRow>) : null }
    { showDirectProof ? (<AppRow><RProof /></AppRow>) : null }
    { showInductiveProof ? (<AppRow><RBaseCase /></AppRow>) : null }
    { showInductiveProof ? (<AppRow><RInductiveCase /></AppRow>) : null }
  </div>
)

export default App

