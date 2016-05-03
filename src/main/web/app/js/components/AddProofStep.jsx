import React from 'react'
import FormulaInput from './FormulaInput'

class AddProofStep extends React.Component {
  
  constructor(props) {
    super(props)
    const { 
      onCheckButtonClick = () => {}
    } = props
    this.justificationUiIds = this.justificationUiIds.bind(this)
    this.justificationIds = this.justificationIds.bind(this)
    this.state = { formula: '' }
    this.click = () => onCheckButtonClick(this.state.formula, this.justificationIds())
  }

  justificationUiIds() {
    return this.props.justification.map(j => j.uiId)
  }

  justificationIds() {
    return this.props.justification.map(j => j.id)
  }

  render() {
    return (
      <div>
        <input onChange={ (e) => this.setState({ formula: e.target.value }) } />
        <div>
          [from { this.justificationUiIds().join(', ') }]
        </div>
        { this.state.formula && this.justificationIds().length > 0 ? 
            <button onClick={this.click}>
              Check
            </button>
            : null
        }
      </div>
    )
  }

}

export default AddProofStep

