import React from 'react'
import AppRow from './AppRow'
import RFunctionInput from '../containers/RFunctionInput'
import RToShow from '../containers/RToShow' 
import RGiven from '../containers/RGiven'
import RProof from '../containers/RProof'

    // <AppRow rowClass="top-buffer"><RFunctionInput /></AppRow>
    // <AppRow><RBaseCase /></AppRow>
    // <AppRow><RInductiveCase /></AppRow>

const App = ({ showGiven, showProof }) => (
  <div className="container">
    <AppRow rowClass="top-buffer"><RToShow /></AppRow>
    { showGiven ? (<AppRow><RGiven /></AppRow>) : null }
    { showProof ? (<AppRow><RProof /></AppRow>) : null }
  </div>
)

export default App

