import React from 'react'
import AppRow from './AppRow'
import RFunctionInput from '../containers/RFunctionInput'
import RToShow from '../containers/RToShow' 
import RGiven from '../containers/RGiven'
import RProof from '../containers/RProof'

    // <AppRow rowClass="top-buffer"><RFunctionInput /></AppRow>
    // <AppRow><RBaseCase /></AppRow>
    // <AppRow><RInductiveCase /></AppRow>

const App = () => (
  <div className="container">
    <AppRow rowClass="top-buffer"><RToShow /></AppRow>
    <AppRow><RGiven /></AppRow>
    <AppRow><RProof /></AppRow>
  </div>
)

export default App

