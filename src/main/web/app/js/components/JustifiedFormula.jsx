import React from 'react'

const JustifiedFormula = ({ 
  id, 
  uiId, 
  formula, 
  justification, 
  onFormulaClick 
}) => (
  <h4 onClick={() => onFormulaClick(id)}>
    ({ uiId }) { formula } [from { justification.join(', ') }]
  </h4>
)

export default JustifiedFormula

