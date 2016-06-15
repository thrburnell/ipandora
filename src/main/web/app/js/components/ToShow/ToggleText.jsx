import React from 'react'
import { PROOF_MODE } from '../../constants'

const ToggleText = ({ mode, knownValid, onToggleClick }) => {
  const text = mode == PROOF_MODE.INDUCTION ? "By direct" : "By induction"
  return knownValid ? null : (
    <p className="panel-title pull-right">
      <a href="#" onClick={(e) => { onToggleClick(); e.preventDefault(); }}>{ text }</a>
    </p>
  )
}

export default ToggleText

