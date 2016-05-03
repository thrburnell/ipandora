import React from 'react'

const JustifiedFormula = ({ uiId, formula, justification }) => (
  <h4>({ uiId }) { formula } [from { justification.join(', ') }]</h4>
)

export default JustifiedFormula

