import React from 'react'
import RProofStructUpload from '../containers/RProofStructUpload'
import GivenBlock from './GivenBlock'
import ToShowBlock from './ToShowBlock'
import ProofBlock from './ProofBlock'
import Separator from './Separator'

const App = () => (
  <div>
    <RProofStructUpload />
    <GivenBlock />
    <ToShowBlock />
    <Separator />
    <ProofBlock />
  </div>
)

export default App

