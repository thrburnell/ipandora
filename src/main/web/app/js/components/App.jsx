import React from 'react'
import AppRow from './AppRow'
import RFunctionInput from '../containers/RFunctionInput'
import RToShow from '../containers/RToShow' 
import RBaseCase from '../containers/RBaseCase'
import RInductiveCase from '../containers/RInductiveCase'

    // <AppRow rowClass="top-buffer"><RFunctionInput /></AppRow>
    // <AppRow><RBaseCase /></AppRow>
    // <AppRow><RInductiveCase /></AppRow>

const App = () => (
  <div className="container">
    <AppRow rowClass="top-buffer"><RToShow /></AppRow>
  </div>
)

export default App

