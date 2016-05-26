import React from 'react'
import RProofStructUpload from '../containers/RProofStructUpload'
import RClearButton from '../containers/RClearButton'
import GivenBlock from './GivenBlock'
import ToShowBlock from './ToShowBlock'
import ProofBlock from './ProofBlock'
import Separator from './Separator'

const App = () => (
  <div>
    <RProofStructUpload />
    <RClearButton />
    <GivenBlock />
    <ToShowBlock />
    <Separator />
    <ProofBlock />
  </div>
)

export default App

