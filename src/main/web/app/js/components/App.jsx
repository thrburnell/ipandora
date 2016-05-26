import React from 'react'
import AppRow from './AppRow'
import RFunctionInput from '../containers/RFunctionInput'
import RToShow from '../containers/RToShow' 
import RBaseCase from '../containers/RBaseCase'
import RInductiveCase from '../containers/RInductiveCase'

const App = () => (
  <div className="container">
    <AppRow rowClass="top-buffer"><RFunctionInput /></AppRow>
    <AppRow><RToShow /></AppRow>
    <AppRow><RBaseCase /></AppRow>
    <AppRow><RInductiveCase /></AppRow>
  </div>
)

export default App

